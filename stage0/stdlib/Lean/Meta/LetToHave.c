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
lean_object* v___x_1403_; lean_object* v_env_1404_; lean_object* v___x_1405_; lean_object* v_toCold_1406_; lean_object* v_mctx_1407_; lean_object* v_lctx_1408_; lean_object* v_options_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1403_ = lean_st_ref_get(v___y_1401_);
v_env_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref(v_env_1404_);
lean_dec(v___x_1403_);
v___x_1405_ = lean_st_ref_get(v___y_1399_);
v_toCold_1406_ = lean_ctor_get(v___y_1400_, 0);
v_mctx_1407_ = lean_ctor_get(v___x_1405_, 0);
lean_inc_ref(v_mctx_1407_);
lean_dec(v___x_1405_);
v_lctx_1408_ = lean_ctor_get(v___y_1398_, 2);
v_options_1409_ = lean_ctor_get(v_toCold_1406_, 2);
lean_inc_ref(v_options_1409_);
lean_inc_ref(v_lctx_1408_);
v___x_1410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1410_, 0, v_env_1404_);
lean_ctor_set(v___x_1410_, 1, v_mctx_1407_);
lean_ctor_set(v___x_1410_, 2, v_lctx_1408_);
lean_ctor_set(v___x_1410_, 3, v_options_1409_);
v___x_1411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v_msgData_1397_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_ref_1426_; lean_object* v___x_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_ref_1426_ = lean_ctor_get(v___y_1423_, 2);
v___x_1427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_inc(v_ref_1426_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_ref_1426_);
lean_ctor_set(v___x_1432_, 1, v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 1);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1444_, lean_object* v_msg_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_toCold_1453_; lean_object* v_currRecDepth_1454_; lean_object* v_ref_1455_; uint8_t v_diag_1456_; uint8_t v_suppressElabErrors_1457_; lean_object* v_ref_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_toCold_1453_ = lean_ctor_get(v___y_1450_, 0);
v_currRecDepth_1454_ = lean_ctor_get(v___y_1450_, 1);
v_ref_1455_ = lean_ctor_get(v___y_1450_, 2);
v_diag_1456_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*3);
v_suppressElabErrors_1457_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*3 + 1);
v_ref_1458_ = l_Lean_replaceRef(v_ref_1444_, v_ref_1455_);
lean_inc(v_currRecDepth_1454_);
lean_inc_ref(v_toCold_1453_);
v___x_1459_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1459_, 0, v_toCold_1453_);
lean_ctor_set(v___x_1459_, 1, v_currRecDepth_1454_);
lean_ctor_set(v___x_1459_, 2, v_ref_1458_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*3, v_diag_1456_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*3 + 1, v_suppressElabErrors_1457_);
v___x_1460_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1445_, v___y_1448_, v___y_1449_, v___x_1459_, v___y_1451_);
lean_dec_ref_known(v___x_1459_, 3);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1461_, lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1461_, v_msg_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v_ref_1461_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v_declHint_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v_a_1482_; lean_object* v___x_1483_; 
v___x_1481_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1472_, v_declHint_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1471_, v_a_1482_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1484_, lean_object* v_msg_1485_, lean_object* v_declHint_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1484_, v_msg_1485_, v_declHint_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec(v_ref_1484_);
return v_res_1494_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1500_ = l_Lean_stringToMessageData(v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1501_, lean_object* v_constName_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1510_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1511_ = 0;
lean_inc(v_constName_1502_);
v___x_1512_ = l_Lean_MessageData_ofConstName(v_constName_1502_, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1510_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1501_, v___x_1515_, v_constName_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1517_, lean_object* v_constName_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1517_, v_constName_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v_ref_1517_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_ref_1535_; lean_object* v___x_1536_; 
v_ref_1535_ = lean_ctor_get(v___y_1532_, 2);
v___x_1536_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1535_, v_constName_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec(v___y_1538_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v_env_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = lean_st_ref_get(v___y_1552_);
v_env_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc_ref(v_env_1555_);
lean_dec(v___x_1554_);
v___x_1556_ = 0;
lean_inc(v_constName_1546_);
v___x_1557_ = l_Lean_Environment_findConstVal_x3f(v_env_1555_, v_constName_1546_, v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1558_;
}
else
{
lean_object* v_val_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_constName_1546_);
v_val_1559_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1557_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_val_1559_);
lean_dec(v___x_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 0);
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_val_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v___y_1568_);
return v_res_1575_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1580_ = lean_unsigned_to_nat(35u);
v___x_1581_ = lean_unsigned_to_nat(203u);
v___x_1582_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1584_ = l_mkPanicMessageWithDecl(v___x_1583_, v___x_1582_, v___x_1581_, v___x_1580_, v___x_1579_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
if (lean_obj_tag(v_e_1585_) == 4)
{
lean_object* v_declName_1593_; lean_object* v_us_1594_; lean_object* v___x_1595_; 
v_declName_1593_ = lean_ctor_get(v_e_1585_, 0);
v_us_1594_ = lean_ctor_get(v_e_1585_, 1);
lean_inc(v_declName_1593_);
v___x_1595_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1593_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v_levelParams_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v_levelParams_1597_ = lean_ctor_get(v_a_1596_, 1);
v___x_1598_ = l_List_lengthTR___redArg(v_levelParams_1597_);
v___x_1599_ = l_List_lengthTR___redArg(v_us_1594_);
v___x_1600_ = lean_nat_dec_eq(v___x_1598_, v___x_1599_);
lean_dec(v___x_1599_);
lean_dec(v___x_1598_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_inc(v_us_1594_);
lean_inc(v_declName_1593_);
lean_dec(v_a_1596_);
lean_dec_ref_known(v_e_1585_, 2);
v___x_1601_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1593_, v_us_1594_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; 
lean_inc(v_us_1594_);
v___x_1602_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1596_, v_us_1594_, v___y_1591_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1612_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_a_1603_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_e_1585_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1608_);
v___x_1610_ = v___x_1605_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref_known(v_e_1585_, 2);
v_a_1613_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1602_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1602_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref_known(v_e_1585_, 2);
v_a_1621_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1595_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1595_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec_ref(v_e_1585_);
v___x_1629_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1630_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1629_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec(v___y_1632_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___y_1648_; lean_object* v___x_1649_; 
lean_inc_ref(v_e_1640_);
v___y_1648_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1648_, 0, v_e_1640_);
v___x_1649_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1640_, v___y_1648_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec(v_a_1651_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1659_, lean_object* v_constName_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_constName_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1669_, v_constName_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1679_, lean_object* v_ref_1680_, lean_object* v_constName_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1680_, v_constName_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1690_, lean_object* v_ref_1691_, lean_object* v_constName_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1690_, v_ref_1691_, v_constName_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec(v_ref_1691_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1701_, lean_object* v_ref_1702_, lean_object* v_msg_1703_, lean_object* v_declHint_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1702_, v_msg_1703_, v_declHint_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_ref_1714_, lean_object* v_msg_1715_, lean_object* v_declHint_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1713_, v_ref_1714_, v_msg_1715_, v_declHint_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec(v_ref_1714_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1725_, lean_object* v_declHint_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1725_, v_declHint_1726_, v___y_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1735_, lean_object* v_declHint_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1735_, v_declHint_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec(v___y_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1745_, lean_object* v_ref_1746_, lean_object* v_msg_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1746_, v_msg_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1756_, lean_object* v_ref_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1756_, v_ref_1757_, v_msg_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec(v_ref_1757_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1768_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1777_, lean_object* v_msg_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1777_, v_msg_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec(v___y_1779_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1788_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_r_1787_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; 
lean_inc_ref(v_r_1787_);
v___x_1797_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1787_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1850_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1850_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1850_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_expr_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1848_; 
v_expr_1802_ = lean_ctor_get(v_r_1787_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_r_1787_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v_r_1787_, 1);
lean_dec(v_unused_1849_);
v___x_1804_ = v_r_1787_;
v_isShared_1805_ = v_isSharedCheck_1848_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_expr_1802_);
lean_dec(v_r_1787_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1848_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Lean_Expr_isSort(v_a_1798_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_del_object(v___x_1800_);
lean_inc(v_a_1793_);
lean_inc_ref(v_a_1792_);
lean_inc(v_a_1791_);
lean_inc_ref(v_a_1790_);
v___x_1807_ = lean_whnf(v_a_1798_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1832_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
if (lean_obj_tag(v_a_1808_) == 3)
{
lean_object* v___x_1812_; lean_object* v_count_1813_; lean_object* v_results_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1830_; 
v___x_1812_ = lean_st_ref_take(v_a_1789_);
v_count_1813_ = lean_ctor_get(v___x_1812_, 0);
v_results_1814_ = lean_ctor_get(v___x_1812_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1816_ = v___x_1812_;
v_isShared_1817_ = v_isSharedCheck_1830_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_results_1814_);
lean_inc(v_count_1813_);
lean_dec(v___x_1812_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1830_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_a_1808_);
lean_inc_ref(v_expr_1802_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v___x_1818_);
v___x_1820_ = v___x_1804_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_expr_1802_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_inc_ref(v___x_1820_);
v___x_1821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1814_, v_expr_1802_, v___x_1820_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v___x_1821_);
v___x_1823_ = v___x_1816_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_count_1813_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_st_ref_put(v_a_1789_, v___x_1823_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1820_);
v___x_1826_ = v___x_1810_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1820_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
else
{
lean_object* v___x_1831_; 
lean_del_object(v___x_1810_);
lean_dec(v_a_1808_);
lean_del_object(v___x_1804_);
v___x_1831_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1802_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
return v___x_1831_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_del_object(v___x_1804_);
lean_dec_ref(v_expr_1802_);
v_a_1833_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1807_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1807_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_a_1798_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v___x_1841_);
v___x_1843_ = v___x_1804_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_expr_1802_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1843_);
v___x_1845_ = v___x_1800_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v_r_1787_);
v_a_1851_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1797_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1797_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec(v_a_1860_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = l_Lean_instInhabitedExpr;
v___x_1870_ = lean_panic_fn_borrowed(v___x_1869_, v_msg_1868_);
return v___x_1870_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1875_ = lean_unsigned_to_nat(18u);
v___x_1876_ = lean_unsigned_to_nat(1847u);
v___x_1877_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1879_ = l_mkPanicMessageWithDecl(v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_, v___x_1874_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1880_, lean_object* v_f_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___y_1891_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1904_; lean_object* v_fType_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; uint8_t v___x_1965_; 
v___x_1965_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1883_);
if (v___x_1965_ == 0)
{
if (lean_obj_tag(v_e_1880_) == 5)
{
lean_object* v_expr_1966_; lean_object* v_expr_1967_; lean_object* v_fn_1968_; lean_object* v_arg_1969_; size_t v___x_1970_; size_t v___x_1971_; uint8_t v___x_1972_; 
v_expr_1966_ = lean_ctor_get(v_f_1881_, 0);
lean_inc_ref(v_expr_1966_);
lean_dec_ref(v_f_1881_);
v_expr_1967_ = lean_ctor_get(v_a_1882_, 0);
lean_inc_ref(v_expr_1967_);
lean_dec_ref(v_a_1882_);
v_fn_1968_ = lean_ctor_get(v_e_1880_, 0);
v_arg_1969_ = lean_ctor_get(v_e_1880_, 1);
v___x_1970_ = lean_ptr_addr(v_fn_1968_);
v___x_1971_ = lean_ptr_addr(v_expr_1966_);
v___x_1972_ = lean_usize_dec_eq(v___x_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref_known(v_e_1880_, 2);
v___x_1973_ = l_Lean_Expr_app___override(v_expr_1966_, v_expr_1967_);
v___y_1891_ = v___x_1973_;
goto v___jp_1890_;
}
else
{
size_t v___x_1974_; size_t v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = lean_ptr_addr(v_arg_1969_);
v___x_1975_ = lean_ptr_addr(v_expr_1967_);
v___x_1976_ = lean_usize_dec_eq(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec_ref_known(v_e_1880_, 2);
v___x_1977_ = l_Lean_Expr_app___override(v_expr_1966_, v_expr_1967_);
v___y_1891_ = v___x_1977_;
goto v___jp_1890_;
}
else
{
lean_dec_ref(v_expr_1967_);
lean_dec_ref(v_expr_1966_);
v___y_1891_ = v_e_1880_;
goto v___jp_1890_;
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v_a_1882_);
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_e_1880_);
v___x_1978_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1979_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1978_);
v___y_1891_ = v___x_1979_;
goto v___jp_1890_;
}
}
else
{
lean_object* v___x_1980_; 
lean_inc_ref(v_f_1881_);
v___x_1980_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1881_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; uint8_t v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = l_Lean_Expr_isForall(v_a_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_inc(v_a_1888_);
lean_inc_ref(v_a_1887_);
lean_inc(v_a_1886_);
lean_inc_ref(v_a_1885_);
v___x_1983_ = lean_whnf(v_a_1981_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v_fType_1921_ = v_a_1984_;
v___y_1922_ = v_a_1884_;
v___y_1923_ = v_a_1885_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
v___y_1926_ = v_a_1888_;
goto v___jp_1920_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v_a_1882_);
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_e_1880_);
v_a_1985_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1983_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
v_fType_1921_ = v_a_1981_;
v___y_1922_ = v_a_1884_;
v___y_1923_ = v_a_1885_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
v___y_1926_ = v_a_1888_;
goto v___jp_1920_;
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_a_1882_);
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_e_1880_);
v_a_1993_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1980_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1980_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
v___jp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___y_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
v___jp_1895_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1899_ = lean_expr_instantiate1(v___y_1896_, v___y_1897_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v___y_1896_);
v___x_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___y_1898_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
v___jp_1903_:
{
if (lean_obj_tag(v_e_1880_) == 5)
{
lean_object* v_expr_1905_; lean_object* v_expr_1906_; lean_object* v_fn_1907_; lean_object* v_arg_1908_; size_t v___x_1909_; size_t v___x_1910_; uint8_t v___x_1911_; 
v_expr_1905_ = lean_ctor_get(v_f_1881_, 0);
lean_inc_ref(v_expr_1905_);
lean_dec_ref(v_f_1881_);
v_expr_1906_ = lean_ctor_get(v_a_1882_, 0);
lean_inc_ref(v_expr_1906_);
lean_dec_ref(v_a_1882_);
v_fn_1907_ = lean_ctor_get(v_e_1880_, 0);
v_arg_1908_ = lean_ctor_get(v_e_1880_, 1);
v___x_1909_ = lean_ptr_addr(v_fn_1907_);
v___x_1910_ = lean_ptr_addr(v_expr_1905_);
v___x_1911_ = lean_usize_dec_eq(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_dec_ref_known(v_e_1880_, 2);
lean_inc_ref(v_expr_1906_);
v___x_1912_ = l_Lean_Expr_app___override(v_expr_1905_, v_expr_1906_);
v___y_1896_ = v___y_1904_;
v___y_1897_ = v_expr_1906_;
v___y_1898_ = v___x_1912_;
goto v___jp_1895_;
}
else
{
size_t v___x_1913_; size_t v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = lean_ptr_addr(v_arg_1908_);
v___x_1914_ = lean_ptr_addr(v_expr_1906_);
v___x_1915_ = lean_usize_dec_eq(v___x_1913_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_dec_ref_known(v_e_1880_, 2);
lean_inc_ref(v_expr_1906_);
v___x_1916_ = l_Lean_Expr_app___override(v_expr_1905_, v_expr_1906_);
v___y_1896_ = v___y_1904_;
v___y_1897_ = v_expr_1906_;
v___y_1898_ = v___x_1916_;
goto v___jp_1895_;
}
else
{
lean_dec_ref(v_expr_1905_);
v___y_1896_ = v___y_1904_;
v___y_1897_ = v_expr_1906_;
v___y_1898_ = v_e_1880_;
goto v___jp_1895_;
}
}
}
else
{
lean_object* v_expr_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_e_1880_);
v_expr_1917_ = lean_ctor_get(v_a_1882_, 0);
lean_inc_ref(v_expr_1917_);
lean_dec_ref(v_a_1882_);
v___x_1918_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1919_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1918_);
v___y_1896_ = v___y_1904_;
v___y_1897_ = v_expr_1917_;
v___y_1898_ = v___x_1919_;
goto v___jp_1895_;
}
}
v___jp_1920_:
{
if (lean_obj_tag(v_fType_1921_) == 7)
{
lean_object* v_binderType_1927_; lean_object* v_body_1928_; lean_object* v___x_1929_; 
v_binderType_1927_ = lean_ctor_get(v_fType_1921_, 1);
lean_inc_ref(v_binderType_1927_);
v_body_1928_ = lean_ctor_get(v_fType_1921_, 2);
lean_inc_ref(v_body_1928_);
lean_dec_ref_known(v_fType_1921_, 3);
lean_inc_ref(v_a_1882_);
v___x_1929_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1882_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = l_Lean_Meta_isExprDefEq(v_binderType_1927_, v_a_1930_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; uint8_t v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = lean_unbox(v_a_1932_);
lean_dec(v_a_1932_);
if (v___x_1933_ == 0)
{
lean_object* v_expr_1934_; lean_object* v_expr_1935_; lean_object* v___x_1936_; 
v_expr_1934_ = lean_ctor_get(v_f_1881_, 0);
v_expr_1935_ = lean_ctor_get(v_a_1882_, 0);
lean_inc_ref(v_expr_1935_);
lean_inc_ref(v_expr_1934_);
v___x_1936_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1934_, v_expr_1935_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v___y_1904_ = v_body_1928_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_body_1928_);
lean_dec_ref(v_a_1882_);
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_e_1880_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
v___y_1904_ = v_body_1928_;
goto v___jp_1903_;
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_body_1928_);
lean_dec_ref(v_a_1882_);
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_e_1880_);
v_a_1945_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1931_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1931_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_body_1928_);
lean_dec_ref(v_binderType_1927_);
lean_dec_ref(v_a_1882_);
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_e_1880_);
v_a_1953_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1929_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1929_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_expr_1961_; lean_object* v_expr_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v_fType_1921_);
lean_dec_ref(v_e_1880_);
v_expr_1961_ = lean_ctor_get(v_f_1881_, 0);
lean_inc_ref(v_expr_1961_);
lean_dec_ref(v_f_1881_);
v_expr_1962_ = lean_ctor_get(v_a_1882_, 0);
lean_inc_ref(v_expr_1962_);
lean_dec_ref(v_a_1882_);
v___x_1963_ = l_Lean_Expr_app___override(v_expr_1961_, v_expr_1962_);
v___x_1964_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1963_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2001_, lean_object* v_f_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2001_, v_f_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec(v_a_2004_);
return v_res_2011_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2014_ = lean_unsigned_to_nat(37u);
v___x_2015_ = lean_unsigned_to_nat(345u);
v___x_2016_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2017_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2018_ = l_mkPanicMessageWithDecl(v___x_2017_, v___x_2016_, v___x_2015_, v___x_2014_, v___x_2013_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2019_, lean_object* v_i_2020_, lean_object* v_a_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_zero_2029_; uint8_t v_isZero_2030_; 
v_zero_2029_ = lean_unsigned_to_nat(0u);
v_isZero_2030_ = lean_nat_dec_eq(v_i_2020_, v_zero_2029_);
if (v_isZero_2030_ == 1)
{
lean_object* v___x_2031_; 
lean_dec(v_i_2020_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_a_2021_);
return v___x_2031_;
}
else
{
lean_object* v_one_2032_; lean_object* v_n_2033_; lean_object* v___y_2035_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___x_2047_; 
v_one_2032_ = lean_unsigned_to_nat(1u);
v_n_2033_ = lean_nat_sub(v_i_2020_, v_one_2032_);
lean_dec(v_i_2020_);
v___x_2047_ = lean_array_fget_borrowed(v_fvars_2019_, v_n_2033_);
if (lean_obj_tag(v___x_2047_) == 1)
{
lean_object* v_fvarId_2048_; lean_object* v___x_2049_; 
v_fvarId_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_fvarId_2048_);
v___x_2049_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2048_, v___y_2024_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
if (lean_obj_tag(v_a_2050_) == 1)
{
lean_object* v_val_2051_; 
v_val_2051_ = lean_ctor_get(v_a_2050_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v_a_2050_, 1);
if (lean_obj_tag(v_val_2051_) == 0)
{
lean_object* v_userName_2052_; lean_object* v_type_2053_; uint8_t v_bi_2054_; lean_object* v_expr_2055_; lean_object* v_type_x3f_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2077_; 
v_userName_2052_ = lean_ctor_get(v_val_2051_, 2);
lean_inc(v_userName_2052_);
v_type_2053_ = lean_ctor_get(v_val_2051_, 3);
lean_inc_ref(v_type_2053_);
v_bi_2054_ = lean_ctor_get_uint8(v_val_2051_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2051_, 4);
v_expr_2055_ = lean_ctor_get(v_a_2021_, 0);
v_type_x3f_2056_ = lean_ctor_get(v_a_2021_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2058_ = v_a_2021_;
v_isShared_2059_ = v_isSharedCheck_2077_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_type_x3f_2056_);
lean_inc(v_expr_2055_);
lean_dec(v_a_2021_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2077_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___y_2063_; 
v___x_2060_ = lean_expr_abstract_range(v_type_2053_, v_n_2033_, v_fvars_2019_);
lean_dec_ref(v_type_2053_);
lean_inc_ref(v___x_2060_);
lean_inc(v_userName_2052_);
v___x_2061_ = l_Lean_Expr_lam___override(v_userName_2052_, v___x_2060_, v_expr_2055_, v_bi_2054_);
if (lean_obj_tag(v_type_x3f_2056_) == 0)
{
lean_dec_ref(v___x_2060_);
lean_dec(v_userName_2052_);
v___y_2063_ = v_type_x3f_2056_;
goto v___jp_2062_;
}
else
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2076_; 
v_val_2068_ = lean_ctor_get(v_type_x3f_2056_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_type_x3f_2056_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2070_ = v_type_x3f_2056_;
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v_type_x3f_2056_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = l_Lean_Expr_forallE___override(v_userName_2052_, v___x_2060_, v_val_2068_, v_bi_2054_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2072_);
v___x_2074_ = v___x_2070_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v___y_2063_ = v___x_2074_;
goto v___jp_2062_;
}
}
}
v___jp_2062_:
{
lean_object* v___x_2065_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___y_2063_);
lean_ctor_set(v___x_2058_, 0, v___x_2061_);
v___x_2065_ = v___x_2058_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___y_2063_);
v___x_2065_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v_i_2020_ = v_n_2033_;
v_a_2021_ = v___x_2065_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2078_; lean_object* v_type_2079_; lean_object* v_value_2080_; uint8_t v_nondep_2081_; uint8_t v_nondep_2083_; lean_object* v___x_2093_; 
v_userName_2078_ = lean_ctor_get(v_val_2051_, 2);
lean_inc(v_userName_2078_);
v_type_2079_ = lean_ctor_get(v_val_2051_, 3);
lean_inc_ref(v_type_2079_);
v_value_2080_ = lean_ctor_get(v_val_2051_, 4);
lean_inc_ref(v_value_2080_);
v_nondep_2081_ = lean_ctor_get_uint8(v_val_2051_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2051_, 5);
v___x_2093_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2025_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; uint8_t v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = 1;
if (v_nondep_2081_ == 0)
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2048_, v_a_2094_);
lean_dec(v_a_2094_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2023_);
lean_dec_ref(v___x_2097_);
v_nondep_2083_ = v___x_2095_;
goto v___jp_2082_;
}
else
{
v_nondep_2083_ = v_nondep_2081_;
goto v___jp_2082_;
}
}
else
{
lean_dec(v_a_2094_);
v_nondep_2083_ = v___x_2095_;
goto v___jp_2082_;
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref(v_value_2080_);
lean_dec_ref(v_type_2079_);
lean_dec(v_userName_2078_);
lean_dec(v_n_2033_);
lean_dec_ref(v_a_2021_);
v_a_2098_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2093_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2093_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
v___jp_2082_:
{
lean_object* v_expr_2084_; lean_object* v_type_x3f_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_expr_2084_ = lean_ctor_get(v_a_2021_, 0);
lean_inc_ref(v_expr_2084_);
v_type_x3f_2085_ = lean_ctor_get(v_a_2021_, 1);
lean_inc(v_type_x3f_2085_);
lean_dec_ref(v_a_2021_);
v___x_2086_ = lean_expr_abstract_range(v_type_2079_, v_n_2033_, v_fvars_2019_);
lean_dec_ref(v_type_2079_);
v___x_2087_ = lean_expr_abstract_range(v_value_2080_, v_n_2033_, v_fvars_2019_);
lean_dec_ref(v_value_2080_);
lean_inc_ref(v___x_2087_);
lean_inc_ref(v___x_2086_);
lean_inc(v_userName_2078_);
v___x_2088_ = l_Lean_Expr_letE___override(v_userName_2078_, v___x_2086_, v___x_2087_, v_expr_2084_, v_nondep_2083_);
if (lean_obj_tag(v_type_x3f_2085_) == 0)
{
lean_dec_ref(v___x_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_userName_2078_);
v___y_2039_ = v___x_2088_;
v___y_2040_ = v_type_x3f_2085_;
goto v___jp_2038_;
}
else
{
lean_object* v_val_2089_; uint8_t v___x_2090_; 
v_val_2089_ = lean_ctor_get(v_type_x3f_2085_, 0);
lean_inc(v_val_2089_);
lean_dec_ref_known(v_type_x3f_2085_, 1);
v___x_2090_ = lean_expr_has_loose_bvar(v_val_2089_, v_zero_2029_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref(v___x_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_userName_2078_);
v___x_2091_ = lean_expr_lower_loose_bvars(v_val_2089_, v_one_2032_, v_one_2032_);
lean_dec(v_val_2089_);
v___y_2044_ = v___x_2088_;
v___y_2045_ = v___x_2091_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_Expr_letE___override(v_userName_2078_, v___x_2086_, v___x_2087_, v_val_2089_, v_nondep_2083_);
v___y_2044_ = v___x_2088_;
v___y_2045_ = v___x_2092_;
goto v___jp_2043_;
}
}
}
}
}
else
{
lean_object* v___x_2106_; 
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2021_);
lean_inc(v_fvarId_2048_);
v___x_2106_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2048_, v___y_2026_, v___y_2027_);
v___y_2035_ = v___x_2106_;
goto v___jp_2034_;
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_n_2033_);
lean_dec_ref(v_a_2021_);
v_a_2107_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2049_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2049_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v_a_2021_);
v___x_2115_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2116_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2115_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
v___y_2035_ = v___x_2116_;
goto v___jp_2034_;
}
v___jp_2034_:
{
if (lean_obj_tag(v___y_2035_) == 0)
{
lean_object* v_a_2036_; 
v_a_2036_ = lean_ctor_get(v___y_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___y_2035_, 1);
v_i_2020_ = v_n_2033_;
v_a_2021_ = v_a_2036_;
goto _start;
}
else
{
lean_dec(v_n_2033_);
return v___y_2035_;
}
}
v___jp_2038_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___y_2039_);
lean_ctor_set(v___x_2041_, 1, v___y_2040_);
v_i_2020_ = v_n_2033_;
v_a_2021_ = v___x_2041_;
goto _start;
}
v___jp_2043_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___y_2045_);
v___y_2039_ = v___y_2044_;
v___y_2040_ = v___x_2046_;
goto v___jp_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2117_, lean_object* v_i_2118_, lean_object* v_a_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2117_, v_i_2118_, v_a_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v_fvars_2117_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
if (lean_obj_tag(v_a_2128_) == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = l_List_reverse___redArg(v_a_2129_);
return v___x_2130_;
}
else
{
lean_object* v_head_2131_; lean_object* v_tail_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2141_; 
v_head_2131_ = lean_ctor_get(v_a_2128_, 0);
v_tail_2132_ = lean_ctor_get(v_a_2128_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2134_ = v_a_2128_;
v_isShared_2135_ = v_isSharedCheck_2141_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_tail_2132_);
lean_inc(v_head_2131_);
lean_dec(v_a_2128_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2141_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = l_Lean_MessageData_ofExpr(v_head_2131_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 1, v_a_2129_);
lean_ctor_set(v___x_2134_, 0, v___x_2136_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_a_2129_);
v___x_2138_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
v_a_2128_ = v_tail_2132_;
v_a_2129_ = v___x_2138_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2142_; double v___x_2143_; 
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_float_of_nat(v___x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2147_, lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_ref_2154_; lean_object* v___x_2155_; lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2200_; 
v_ref_2154_ = lean_ctor_get(v___y_2151_, 2);
v___x_2155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2200_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2200_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v_traceState_2161_; lean_object* v_env_2162_; lean_object* v_nextMacroScope_2163_; lean_object* v_ngen_2164_; lean_object* v_auxDeclNGen_2165_; lean_object* v_cache_2166_; lean_object* v_messages_2167_; lean_object* v_infoState_2168_; lean_object* v_snapshotTasks_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2199_; 
v___x_2160_ = lean_st_ref_take(v___y_2152_);
v_traceState_2161_ = lean_ctor_get(v___x_2160_, 4);
v_env_2162_ = lean_ctor_get(v___x_2160_, 0);
v_nextMacroScope_2163_ = lean_ctor_get(v___x_2160_, 1);
v_ngen_2164_ = lean_ctor_get(v___x_2160_, 2);
v_auxDeclNGen_2165_ = lean_ctor_get(v___x_2160_, 3);
v_cache_2166_ = lean_ctor_get(v___x_2160_, 5);
v_messages_2167_ = lean_ctor_get(v___x_2160_, 6);
v_infoState_2168_ = lean_ctor_get(v___x_2160_, 7);
v_snapshotTasks_2169_ = lean_ctor_get(v___x_2160_, 8);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2171_ = v___x_2160_;
v_isShared_2172_ = v_isSharedCheck_2199_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_snapshotTasks_2169_);
lean_inc(v_infoState_2168_);
lean_inc(v_messages_2167_);
lean_inc(v_cache_2166_);
lean_inc(v_traceState_2161_);
lean_inc(v_auxDeclNGen_2165_);
lean_inc(v_ngen_2164_);
lean_inc(v_nextMacroScope_2163_);
lean_inc(v_env_2162_);
lean_dec(v___x_2160_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2199_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
uint64_t v_tid_2173_; lean_object* v_traces_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2198_; 
v_tid_2173_ = lean_ctor_get_uint64(v_traceState_2161_, sizeof(void*)*1);
v_traces_2174_ = lean_ctor_get(v_traceState_2161_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_traceState_2161_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2176_ = v_traceState_2161_;
v_isShared_2177_ = v_isSharedCheck_2198_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_traces_2174_);
lean_dec(v_traceState_2161_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2198_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; double v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2180_ = 0;
v___x_2181_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2182_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2182_, 0, v_cls_2147_);
lean_ctor_set(v___x_2182_, 1, v___x_2178_);
lean_ctor_set(v___x_2182_, 2, v___x_2181_);
lean_ctor_set_float(v___x_2182_, sizeof(void*)*3, v___x_2179_);
lean_ctor_set_float(v___x_2182_, sizeof(void*)*3 + 8, v___x_2179_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*3 + 16, v___x_2180_);
v___x_2183_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2184_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v_a_2156_);
lean_ctor_set(v___x_2184_, 2, v___x_2183_);
lean_inc(v_ref_2154_);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_ref_2154_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_PersistentArray_push___redArg(v_traces_2174_, v___x_2185_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2186_);
v___x_2188_ = v___x_2176_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2186_);
lean_ctor_set_uint64(v_reuseFailAlloc_2197_, sizeof(void*)*1, v_tid_2173_);
v___x_2188_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2190_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 4, v___x_2188_);
v___x_2190_ = v___x_2171_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_env_2162_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_nextMacroScope_2163_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_ngen_2164_);
lean_ctor_set(v_reuseFailAlloc_2196_, 3, v_auxDeclNGen_2165_);
lean_ctor_set(v_reuseFailAlloc_2196_, 4, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2196_, 5, v_cache_2166_);
lean_ctor_set(v_reuseFailAlloc_2196_, 6, v_messages_2167_);
lean_ctor_set(v_reuseFailAlloc_2196_, 7, v_infoState_2168_);
lean_ctor_set(v_reuseFailAlloc_2196_, 8, v_snapshotTasks_2169_);
v___x_2190_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2191_ = lean_st_ref_put(v___y_2152_, v___x_2190_);
v___x_2192_ = lean_box(0);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2192_);
v___x_2194_ = v___x_2158_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2201_, lean_object* v_msg_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2201_, v_msg_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
return v_res_2208_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_cls_2219_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2220_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2221_ = l_Lean_Name_append(v___x_2220_, v_cls_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2235_ = l_Lean_MessageData_ofFormat(v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2236_, lean_object* v_body_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v_toCold_2276_; lean_object* v_options_2277_; uint8_t v_hasTrace_2278_; 
v_toCold_2276_ = lean_ctor_get(v_a_2242_, 0);
v_options_2277_ = lean_ctor_get(v_toCold_2276_, 2);
v_hasTrace_2278_ = lean_ctor_get_uint8(v_options_2277_, sizeof(void*)*1);
if (v_hasTrace_2278_ == 0)
{
v___y_2258_ = v_a_2238_;
v___y_2259_ = v_a_2239_;
v___y_2260_ = v_a_2240_;
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
goto v___jp_2257_;
}
else
{
lean_object* v_inheritedTraceOptions_2279_; lean_object* v_cls_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_inheritedTraceOptions_2279_ = lean_ctor_get(v_toCold_2276_, 11);
v_cls_2280_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2281_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2282_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2279_, v_options_2277_, v___x_2281_);
if (v___x_2282_ == 0)
{
v___y_2258_ = v_a_2238_;
v___y_2259_ = v_a_2239_;
v___y_2260_ = v_a_2240_;
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
goto v___jp_2257_;
}
else
{
lean_object* v_expr_2283_; lean_object* v_type_x3f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___y_2297_; 
v_expr_2283_ = lean_ctor_get(v_body_2237_, 0);
v_type_x3f_2284_ = lean_ctor_get(v_body_2237_, 1);
v___x_2285_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2236_);
v___x_2286_ = lean_array_to_list(v_fvars_2236_);
v___x_2287_ = lean_box(0);
v___x_2288_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2286_, v___x_2287_);
v___x_2289_ = l_Lean_MessageData_ofList(v___x_2288_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2285_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
lean_inc_ref(v_expr_2283_);
v___x_2293_ = l_Lean_MessageData_ofExpr(v_expr_2283_);
v___x_2294_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
if (lean_obj_tag(v_type_x3f_2284_) == 0)
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2297_ = v___x_2310_;
goto v___jp_2296_;
}
else
{
lean_object* v_val_2311_; lean_object* v___x_2312_; 
v_val_2311_ = lean_ctor_get(v_type_x3f_2284_, 0);
lean_inc(v_val_2311_);
v___x_2312_ = l_Lean_MessageData_ofExpr(v_val_2311_);
v___y_2297_ = v___x_2312_;
goto v___jp_2296_;
}
v___jp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2295_);
lean_ctor_set(v___x_2298_, 1, v___y_2297_);
v___x_2299_ = l_Lean_indentD(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2292_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2280_, v___x_2300_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_dec_ref_known(v___x_2301_, 1);
v___y_2258_ = v_a_2238_;
v___y_2259_ = v_a_2239_;
v___y_2260_ = v_a_2240_;
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_body_2237_);
lean_dec_ref(v_fvars_2236_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
v___jp_2245_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___y_2252_);
lean_ctor_set(v___x_2254_, 1, v___y_2253_);
v___x_2255_ = lean_array_get_size(v_fvars_2236_);
v___x_2256_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2236_, v___x_2255_, v___x_2254_, v___y_2247_, v___y_2251_, v___y_2249_, v___y_2246_, v___y_2248_, v___y_2250_);
lean_dec_ref(v_fvars_2236_);
return v___x_2256_;
}
v___jp_2257_:
{
lean_object* v_expr_2264_; lean_object* v_type_x3f_2265_; lean_object* v___x_2266_; 
v_expr_2264_ = lean_ctor_get(v_body_2237_, 0);
lean_inc_ref(v_expr_2264_);
v_type_x3f_2265_ = lean_ctor_get(v_body_2237_, 1);
lean_inc(v_type_x3f_2265_);
lean_dec_ref(v_body_2237_);
v___x_2266_ = lean_expr_abstract(v_expr_2264_, v_fvars_2236_);
lean_dec_ref(v_expr_2264_);
if (lean_obj_tag(v_type_x3f_2265_) == 0)
{
v___y_2246_ = v___y_2261_;
v___y_2247_ = v___y_2258_;
v___y_2248_ = v___y_2262_;
v___y_2249_ = v___y_2260_;
v___y_2250_ = v___y_2263_;
v___y_2251_ = v___y_2259_;
v___y_2252_ = v___x_2266_;
v___y_2253_ = v_type_x3f_2265_;
goto v___jp_2245_;
}
else
{
lean_object* v_val_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2275_; 
v_val_2267_ = lean_ctor_get(v_type_x3f_2265_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_type_x3f_2265_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2269_ = v_type_x3f_2265_;
v_isShared_2270_ = v_isSharedCheck_2275_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_val_2267_);
lean_dec(v_type_x3f_2265_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2275_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2271_ = lean_expr_abstract(v_val_2267_, v_fvars_2236_);
lean_dec(v_val_2267_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2271_);
v___x_2273_ = v___x_2269_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
v___y_2246_ = v___y_2261_;
v___y_2247_ = v___y_2258_;
v___y_2248_ = v___y_2262_;
v___y_2249_ = v___y_2260_;
v___y_2250_ = v___y_2263_;
v___y_2251_ = v___y_2259_;
v___y_2252_ = v___x_2266_;
v___y_2253_ = v___x_2273_;
goto v___jp_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2313_, lean_object* v_body_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2313_, v_body_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec(v_a_2315_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2323_, lean_object* v_n_2324_, lean_object* v_i_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2323_, v_i_2325_, v_a_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2336_, lean_object* v_n_2337_, lean_object* v_i_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2336_, v_n_2337_, v_i_2338_, v_a_2339_, v_a_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec(v_n_2337_);
lean_dec_ref(v_fvars_2336_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2349_, lean_object* v_msg_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2349_, v_msg_2350_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2359_, lean_object* v_msg_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2359_, v_msg_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
return v_res_2368_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2375_, lean_object* v_structName_2376_, lean_object* v_idx_2377_, lean_object* v_a_2378_, lean_object* v_00_u03b1_2379_, lean_object* v_x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_expr_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2403_; 
v_expr_2388_ = lean_ctor_get(v_struct_2375_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_struct_2375_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_struct_2375_, 1);
lean_dec(v_unused_2404_);
v___x_2390_ = v_struct_2375_;
v_isShared_2391_ = v_isSharedCheck_2403_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_expr_2388_);
lean_dec(v_struct_2375_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2403_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2392_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2393_ = l_Lean_mkProj(v_structName_2376_, v_idx_2377_, v_expr_2388_);
v___x_2394_ = l_Lean_indentExpr(v___x_2393_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 7);
lean_ctor_set(v___x_2390_, 1, v___x_2394_);
lean_ctor_set(v___x_2390_, 0, v___x_2392_);
v___x_2396_ = v___x_2390_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2397_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = l_Lean_indentExpr(v_a_2378_);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2400_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2405_, lean_object* v_structName_2406_, lean_object* v_idx_2407_, lean_object* v_a_2408_, lean_object* v_00_u03b1_2409_, lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2405_, v_structName_2406_, v_idx_2407_, v_a_2408_, v_00_u03b1_2409_, v_x_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec(v___y_2411_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v_env_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; 
v___x_2427_ = lean_st_ref_get(v___y_2425_);
v_env_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc_ref(v_env_2428_);
lean_dec(v___x_2427_);
v___x_2429_ = 0;
lean_inc(v_constName_2419_);
v___x_2430_ = l_Lean_Environment_find_x3f(v_env_2428_, v_constName_2419_, v___x_2429_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2431_;
}
else
{
lean_object* v_val_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v_constName_2419_);
v_val_2432_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2430_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_val_2432_);
lean_dec(v___x_2430_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 0);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_val_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec(v___y_2441_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2449_, lean_object* v_structName_2450_, lean_object* v_idx_2451_, lean_object* v_a_2452_, lean_object* v_00_u03b1_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_expr_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2477_; 
v_expr_2462_ = lean_ctor_get(v_struct_2449_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_struct_2449_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v_struct_2449_, 1);
lean_dec(v_unused_2478_);
v___x_2464_ = v_struct_2449_;
v_isShared_2465_ = v_isSharedCheck_2477_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_expr_2462_);
lean_dec(v_struct_2449_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2477_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2466_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2467_ = l_Lean_mkProj(v_structName_2450_, v_idx_2451_, v_expr_2462_);
v___x_2468_ = l_Lean_indentExpr(v___x_2467_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 7);
lean_ctor_set(v___x_2464_, 1, v___x_2468_);
lean_ctor_set(v___x_2464_, 0, v___x_2466_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2471_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = l_Lean_indentExpr(v_a_2452_);
v___x_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2474_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2479_, lean_object* v_structName_2480_, lean_object* v_idx_2481_, lean_object* v_a_2482_, lean_object* v_00_u03b1_2483_, lean_object* v_x_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2479_, v_structName_2480_, v_idx_2481_, v_a_2482_, v_00_u03b1_2483_, v_x_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2493_, lean_object* v_fst_2494_, lean_object* v_struct_2495_, lean_object* v_structName_2496_, uint8_t v_a_2497_, lean_object* v___f_2498_, lean_object* v_snd_2499_, lean_object* v_____r_2500_, lean_object* v_ctorType_2501_, lean_object* v_j_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
if (lean_obj_tag(v_ctorType_2501_) == 7)
{
lean_object* v_binderType_2510_; lean_object* v_body_2511_; lean_object* v___x_2512_; 
lean_dec(v_snd_2499_);
v_binderType_2510_ = lean_ctor_get(v_ctorType_2501_, 1);
lean_inc_ref(v_binderType_2510_);
v_body_2511_ = lean_ctor_get(v_ctorType_2501_, 2);
lean_inc_ref(v_body_2511_);
lean_dec_ref_known(v_ctorType_2501_, 3);
v___x_2512_ = lean_expr_instantiate_rev_range(v_binderType_2510_, v_j_2502_, v_a_2493_, v_fst_2494_);
lean_dec_ref(v_binderType_2510_);
if (v_a_2497_ == 0)
{
lean_dec_ref(v___f_2498_);
goto v___jp_2513_;
}
else
{
lean_object* v___x_2529_; 
lean_inc_ref(v___x_2512_);
v___x_2529_ = l_Lean_Meta_isProp(v___x_2512_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; uint8_t v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = lean_unbox(v_a_2530_);
lean_dec(v_a_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_box(0);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc(v___y_2503_);
v___x_2533_ = lean_apply_9(v___f_2498_, lean_box(0), v___x_2532_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, lean_box(0));
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_dec_ref_known(v___x_2533_, 1);
goto v___jp_2513_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref(v___x_2512_);
lean_dec_ref(v_body_2511_);
lean_dec(v_structName_2496_);
lean_dec_ref(v_struct_2495_);
lean_dec(v_fst_2494_);
lean_dec(v_a_2493_);
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2533_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_dec_ref(v___f_2498_);
goto v___jp_2513_;
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v___x_2512_);
lean_dec_ref(v_body_2511_);
lean_dec_ref(v___f_2498_);
lean_dec(v_structName_2496_);
lean_dec_ref(v_struct_2495_);
lean_dec(v_fst_2494_);
lean_dec(v_a_2493_);
v_a_2542_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2529_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2529_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
v___jp_2513_:
{
lean_object* v_expr_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2527_; 
v_expr_2514_ = lean_ctor_get(v_struct_2495_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_struct_2495_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; 
v_unused_2528_ = lean_ctor_get(v_struct_2495_, 1);
lean_dec(v_unused_2528_);
v___x_2516_ = v_struct_2495_;
v_isShared_2517_ = v_isSharedCheck_2527_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_expr_2514_);
lean_dec(v_struct_2495_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2527_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2518_ = l_Lean_Expr_proj___override(v_structName_2496_, v_a_2493_, v_expr_2514_);
v___x_2519_ = lean_array_push(v_fst_2494_, v___x_2518_);
lean_inc(v_j_2502_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 1, v___x_2512_);
lean_ctor_set(v___x_2516_, 0, v_j_2502_);
v___x_2521_ = v___x_2516_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_j_2502_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___x_2512_);
v___x_2521_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2519_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_body_2511_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v_structName_2496_);
lean_dec_ref(v_struct_2495_);
lean_dec(v_a_2493_);
v___x_2550_ = lean_box(0);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc(v___y_2503_);
v___x_2551_ = lean_apply_9(v___f_2498_, lean_box(0), v___x_2550_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, lean_box(0));
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2562_; 
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2551_, 0);
lean_dec(v_unused_2563_);
v___x_2553_ = v___x_2551_;
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
else
{
lean_dec(v___x_2551_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_inc(v_j_2502_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v_j_2502_);
lean_ctor_set(v___x_2555_, 1, v_snd_2499_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v_fst_2494_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v_ctorType_2501_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2558_);
v___x_2560_ = v___x_2553_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref(v_ctorType_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_fst_2494_);
v_a_2564_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2551_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2551_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2572_ = _args[0];
lean_object* v_fst_2573_ = _args[1];
lean_object* v_struct_2574_ = _args[2];
lean_object* v_structName_2575_ = _args[3];
lean_object* v_a_2576_ = _args[4];
lean_object* v___f_2577_ = _args[5];
lean_object* v_snd_2578_ = _args[6];
lean_object* v_____r_2579_ = _args[7];
lean_object* v_ctorType_2580_ = _args[8];
lean_object* v_j_2581_ = _args[9];
lean_object* v___y_2582_ = _args[10];
lean_object* v___y_2583_ = _args[11];
lean_object* v___y_2584_ = _args[12];
lean_object* v___y_2585_ = _args[13];
lean_object* v___y_2586_ = _args[14];
lean_object* v___y_2587_ = _args[15];
lean_object* v___y_2588_ = _args[16];
_start:
{
uint8_t v_a_19024__boxed_2589_; lean_object* v_res_2590_; 
v_a_19024__boxed_2589_ = lean_unbox(v_a_2576_);
v_res_2590_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2572_, v_fst_2573_, v_struct_2574_, v_structName_2575_, v_a_19024__boxed_2589_, v___f_2577_, v_snd_2578_, v_____r_2579_, v_ctorType_2580_, v_j_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec(v_j_2581_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2591_, lean_object* v_struct_2592_, lean_object* v_structName_2593_, uint8_t v_a_2594_, lean_object* v_idx_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___y_2607_; uint8_t v___x_2629_; 
v___x_2629_ = lean_nat_dec_le(v_a_2597_, v_upperBound_2591_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_idx_2595_);
lean_dec(v_structName_2593_);
lean_dec_ref(v_struct_2592_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_b_2598_);
return v___x_2630_;
}
else
{
lean_object* v_snd_2631_; lean_object* v_snd_2632_; lean_object* v_fst_2633_; lean_object* v_fst_2634_; lean_object* v_fst_2635_; lean_object* v_snd_2636_; lean_object* v___f_2637_; uint8_t v___x_2638_; 
v_snd_2631_ = lean_ctor_get(v_b_2598_, 1);
lean_inc(v_snd_2631_);
v_snd_2632_ = lean_ctor_get(v_snd_2631_, 1);
lean_inc(v_snd_2632_);
v_fst_2633_ = lean_ctor_get(v_b_2598_, 0);
lean_inc(v_fst_2633_);
lean_dec_ref(v_b_2598_);
v_fst_2634_ = lean_ctor_get(v_snd_2631_, 0);
lean_inc(v_fst_2634_);
lean_dec(v_snd_2631_);
v_fst_2635_ = lean_ctor_get(v_snd_2632_, 0);
lean_inc(v_fst_2635_);
v_snd_2636_ = lean_ctor_get(v_snd_2632_, 1);
lean_inc(v_snd_2636_);
lean_dec(v_snd_2632_);
lean_inc_ref(v_a_2596_);
lean_inc(v_idx_2595_);
lean_inc(v_structName_2593_);
lean_inc_ref(v_struct_2592_);
v___f_2637_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2637_, 0, v_struct_2592_);
lean_closure_set(v___f_2637_, 1, v_structName_2593_);
lean_closure_set(v___f_2637_, 2, v_idx_2595_);
lean_closure_set(v___f_2637_, 3, v_a_2596_);
v___x_2638_ = l_Lean_Expr_isForall(v_fst_2633_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_expr_instantiate_rev_range(v_fst_2633_, v_fst_2635_, v_a_2597_, v_fst_2634_);
lean_dec(v_fst_2635_);
lean_dec(v_fst_2633_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
v___x_2640_ = lean_whnf(v___x_2639_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = lean_box(0);
lean_inc(v_structName_2593_);
lean_inc_ref(v_struct_2592_);
lean_inc(v_a_2597_);
v___x_2643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2597_, v_fst_2634_, v_struct_2592_, v_structName_2593_, v_a_2594_, v___f_2637_, v_snd_2636_, v___x_2642_, v_a_2641_, v_a_2597_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
v___y_2607_ = v___x_2643_;
goto v___jp_2606_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v___f_2637_);
lean_dec(v_snd_2636_);
lean_dec(v_fst_2634_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_idx_2595_);
lean_dec(v_structName_2593_);
lean_dec_ref(v_struct_2592_);
v_a_2644_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2640_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2640_);
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
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_box(0);
lean_inc(v_structName_2593_);
lean_inc_ref(v_struct_2592_);
lean_inc(v_a_2597_);
v___x_2653_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2597_, v_fst_2634_, v_struct_2592_, v_structName_2593_, v_a_2594_, v___f_2637_, v_snd_2636_, v___x_2652_, v_fst_2633_, v_fst_2635_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v_fst_2635_);
v___y_2607_ = v___x_2653_;
goto v___jp_2606_;
}
}
v___jp_2606_:
{
if (lean_obj_tag(v___y_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2620_; 
v_a_2608_ = lean_ctor_get(v___y_2607_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___y_2607_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2610_ = v___y_2607_;
v_isShared_2611_ = v_isSharedCheck_2620_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___y_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2620_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
if (lean_obj_tag(v_a_2608_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; 
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_idx_2595_);
lean_dec(v_structName_2593_);
lean_dec_ref(v_struct_2592_);
v_a_2612_ = lean_ctor_get(v_a_2608_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v_a_2608_, 1);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v_a_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_del_object(v___x_2610_);
v_a_2616_ = lean_ctor_get(v_a_2608_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v_a_2608_, 1);
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_add(v_a_2597_, v___x_2617_);
lean_dec(v_a_2597_);
v_a_2597_ = v___x_2618_;
v_b_2598_ = v_a_2616_;
goto _start;
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_idx_2595_);
lean_dec(v_structName_2593_);
lean_dec_ref(v_struct_2592_);
v_a_2621_ = lean_ctor_get(v___y_2607_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___y_2607_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___y_2607_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___y_2607_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2654_, lean_object* v_struct_2655_, lean_object* v_structName_2656_, lean_object* v_a_2657_, lean_object* v_idx_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_b_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v_a_19181__boxed_2669_; lean_object* v_res_2670_; 
v_a_19181__boxed_2669_ = lean_unbox(v_a_2657_);
v_res_2670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2654_, v_struct_2655_, v_structName_2656_, v_a_19181__boxed_2669_, v_idx_2658_, v_a_2659_, v_a_2660_, v_b_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec(v_upperBound_2654_);
return v_res_2670_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2673_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2674_ = lean_unsigned_to_nat(18u);
v___x_2675_ = lean_unsigned_to_nat(1896u);
v___x_2676_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2677_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2678_ = l_mkPanicMessageWithDecl(v___x_2677_, v___x_2676_, v___x_2675_, v___x_2674_, v___x_2673_);
return v___x_2678_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v___x_2679_);
return v___x_2681_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v___x_2682_);
return v___x_2684_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2685_; lean_object* v_dummy_2686_; 
v___x_2685_ = lean_box(0);
v_dummy_2686_ = l_Lean_Expr_sort___override(v___x_2685_);
return v_dummy_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2687_, lean_object* v_structName_2688_, lean_object* v_idx_2689_, lean_object* v_struct_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2705_; uint8_t v___x_2709_; 
v___x_2709_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2691_);
if (v___x_2709_ == 0)
{
lean_dec(v_idx_2689_);
lean_dec(v_structName_2688_);
if (lean_obj_tag(v_e_2687_) == 11)
{
lean_object* v_expr_2710_; lean_object* v_typeName_2711_; lean_object* v_idx_2712_; lean_object* v_struct_2713_; size_t v___x_2714_; size_t v___x_2715_; uint8_t v___x_2716_; 
v_expr_2710_ = lean_ctor_get(v_struct_2690_, 0);
lean_inc_ref(v_expr_2710_);
lean_dec_ref(v_struct_2690_);
v_typeName_2711_ = lean_ctor_get(v_e_2687_, 0);
v_idx_2712_ = lean_ctor_get(v_e_2687_, 1);
v_struct_2713_ = lean_ctor_get(v_e_2687_, 2);
v___x_2714_ = lean_ptr_addr(v_struct_2713_);
v___x_2715_ = lean_ptr_addr(v_expr_2710_);
v___x_2716_ = lean_usize_dec_eq(v___x_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; 
lean_inc(v_idx_2712_);
lean_inc(v_typeName_2711_);
lean_dec_ref_known(v_e_2687_, 3);
v___x_2717_ = l_Lean_Expr_proj___override(v_typeName_2711_, v_idx_2712_, v_expr_2710_);
v___y_2705_ = v___x_2717_;
goto v___jp_2704_;
}
else
{
lean_dec_ref(v_expr_2710_);
v___y_2705_ = v_e_2687_;
goto v___jp_2704_;
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec_ref(v_struct_2690_);
lean_dec_ref(v_e_2687_);
v___x_2718_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2719_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2718_);
v___y_2705_ = v___x_2719_;
goto v___jp_2704_;
}
}
else
{
lean_object* v___x_2720_; 
lean_inc_ref(v_struct_2690_);
v___x_2720_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2690_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
lean_inc(v_a_2696_);
lean_inc_ref(v_a_2695_);
lean_inc(v_a_2694_);
lean_inc_ref(v_a_2693_);
v___x_2722_ = lean_whnf(v_a_2721_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc_n(v_a_2723_, 2);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = l_Lean_Meta_isProp(v_a_2723_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = l_Lean_Expr_getAppFn(v_a_2723_);
if (lean_obj_tag(v___x_2726_) == 4)
{
lean_object* v_declName_2727_; lean_object* v_us_2728_; lean_object* v___x_2729_; lean_object* v_env_2733_; uint8_t v___x_2734_; lean_object* v___x_2735_; 
v_declName_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_declName_2727_);
v_us_2728_ = lean_ctor_get(v___x_2726_, 1);
lean_inc(v_us_2728_);
lean_dec_ref_known(v___x_2726_, 2);
v___x_2729_ = lean_st_ref_get(v_a_2696_);
v_env_2733_ = lean_ctor_get(v___x_2729_, 0);
lean_inc_ref(v_env_2733_);
lean_dec(v___x_2729_);
v___x_2734_ = 0;
v___x_2735_ = l_Lean_Environment_find_x3f(v_env_2733_, v_declName_2727_, v___x_2734_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
v___x_2736_ = lean_box(0);
v___x_2737_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2690_, v_structName_2688_, v_idx_2689_, v_a_2723_, lean_box(0), v___x_2736_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2737_;
}
else
{
lean_object* v_val_2738_; 
v_val_2738_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_val_2738_);
lean_dec_ref_known(v___x_2735_, 1);
if (lean_obj_tag(v_val_2738_) == 5)
{
lean_object* v_val_2739_; lean_object* v_ctors_2740_; 
v_val_2739_ = lean_ctor_get(v_val_2738_, 0);
lean_inc_ref(v_val_2739_);
lean_dec_ref_known(v_val_2738_, 1);
v_ctors_2740_ = lean_ctor_get(v_val_2739_, 4);
lean_inc(v_ctors_2740_);
if (lean_obj_tag(v_ctors_2740_) == 1)
{
lean_object* v_tail_2741_; 
v_tail_2741_ = lean_ctor_get(v_ctors_2740_, 1);
if (lean_obj_tag(v_tail_2741_) == 0)
{
lean_object* v_toConstantVal_2742_; lean_object* v_numParams_2743_; lean_object* v_numIndices_2744_; lean_object* v_head_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2854_; 
v_toConstantVal_2742_ = lean_ctor_get(v_val_2739_, 0);
lean_inc_ref(v_toConstantVal_2742_);
v_numParams_2743_ = lean_ctor_get(v_val_2739_, 1);
lean_inc(v_numParams_2743_);
v_numIndices_2744_ = lean_ctor_get(v_val_2739_, 2);
lean_inc(v_numIndices_2744_);
lean_dec_ref(v_val_2739_);
v_head_2745_ = lean_ctor_get(v_ctors_2740_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_ctors_2740_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; 
v_unused_2855_ = lean_ctor_get(v_ctors_2740_, 1);
lean_dec(v_unused_2855_);
v___x_2747_ = v_ctors_2740_;
v_isShared_2748_ = v_isSharedCheck_2854_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_head_2745_);
lean_dec(v_ctors_2740_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2854_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2745_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
if (lean_obj_tag(v_a_2750_) == 6)
{
lean_object* v_val_2751_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v_name_2832_; uint8_t v___x_2833_; 
v_val_2751_ = lean_ctor_get(v_a_2750_, 0);
lean_inc_ref(v_val_2751_);
lean_dec_ref_known(v_a_2750_, 1);
v_name_2832_ = lean_ctor_get(v_toConstantVal_2742_, 0);
lean_inc(v_name_2832_);
lean_dec_ref(v_toConstantVal_2742_);
v___x_2833_ = lean_name_eq(v_name_2832_, v_structName_2688_);
lean_dec(v_name_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref(v_val_2751_);
lean_del_object(v___x_2747_);
lean_dec(v_numIndices_2744_);
lean_dec(v_numParams_2743_);
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
v___x_2834_ = lean_box(0);
v___x_2835_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2690_, v_structName_2688_, v_idx_2689_, v_a_2723_, lean_box(0), v___x_2834_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2835_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2835_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
else
{
v___y_2807_ = v_a_2691_;
v___y_2808_ = v_a_2692_;
v___y_2809_ = v_a_2693_;
v___y_2810_ = v_a_2694_;
v___y_2811_ = v_a_2695_;
v___y_2812_ = v_a_2696_;
goto v___jp_2806_;
}
v___jp_2752_:
{
lean_object* v_toConstantVal_2760_; lean_object* v_name_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_toConstantVal_2760_ = lean_ctor_get(v_val_2751_, 0);
lean_inc_ref(v_toConstantVal_2760_);
lean_dec_ref(v_val_2751_);
v_name_2761_ = lean_ctor_get(v_toConstantVal_2760_, 0);
lean_inc(v_name_2761_);
lean_dec_ref(v_toConstantVal_2760_);
v___x_2762_ = l_Lean_mkConst(v_name_2761_, v_us_2728_);
v___x_2763_ = lean_unsigned_to_nat(0u);
v___x_2764_ = l_Array_toSubarray___redArg(v___y_2753_, v___x_2763_, v_numParams_2743_);
v___x_2765_ = l_Subarray_copy___redArg(v___x_2764_);
v___x_2766_ = l_Lean_mkAppN(v___x_2762_, v___x_2765_);
lean_dec_ref(v___x_2765_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
v___x_2767_ = lean_infer_type(v___x_2766_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 0);
lean_ctor_set(v___x_2747_, 1, v___x_2769_);
lean_ctor_set(v___x_2747_, 0, v_a_2768_);
v___x_2771_ = v___x_2747_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2768_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
uint8_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_unbox(v_a_2725_);
lean_dec(v_a_2725_);
lean_inc_ref(v_struct_2690_);
lean_inc(v_idx_2689_);
v___x_2773_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2689_, v_struct_2690_, v_structName_2688_, v___x_2772_, v_idx_2689_, v_a_2723_, v___x_2763_, v___x_2771_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v_idx_2689_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v_snd_2775_; lean_object* v_snd_2776_; lean_object* v_snd_2777_; lean_object* v_expr_2778_; lean_object* v___x_2779_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v_snd_2775_ = lean_ctor_get(v_a_2774_, 1);
lean_inc(v_snd_2775_);
lean_dec(v_a_2774_);
v_snd_2776_ = lean_ctor_get(v_snd_2775_, 1);
lean_inc(v_snd_2776_);
lean_dec(v_snd_2775_);
v_snd_2777_ = lean_ctor_get(v_snd_2776_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_snd_2776_);
v_expr_2778_ = lean_ctor_get(v_struct_2690_, 0);
lean_inc_ref(v_expr_2778_);
lean_dec_ref(v_struct_2690_);
v___x_2779_ = l_Lean_Expr_cleanupAnnotations(v_snd_2777_);
if (lean_obj_tag(v_e_2687_) == 11)
{
lean_object* v_typeName_2780_; lean_object* v_idx_2781_; lean_object* v_struct_2782_; size_t v___x_2783_; size_t v___x_2784_; uint8_t v___x_2785_; 
v_typeName_2780_ = lean_ctor_get(v_e_2687_, 0);
v_idx_2781_ = lean_ctor_get(v_e_2687_, 1);
v_struct_2782_ = lean_ctor_get(v_e_2687_, 2);
v___x_2783_ = lean_ptr_addr(v_struct_2782_);
v___x_2784_ = lean_ptr_addr(v_expr_2778_);
v___x_2785_ = lean_usize_dec_eq(v___x_2783_, v___x_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; 
lean_inc(v_idx_2781_);
lean_inc(v_typeName_2780_);
lean_dec_ref_known(v_e_2687_, 3);
v___x_2786_ = l_Lean_Expr_proj___override(v_typeName_2780_, v_idx_2781_, v_expr_2778_);
v___y_2699_ = v___x_2779_;
v___y_2700_ = v___x_2786_;
goto v___jp_2698_;
}
else
{
lean_dec_ref(v_expr_2778_);
v___y_2699_ = v___x_2779_;
v___y_2700_ = v_e_2687_;
goto v___jp_2698_;
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec_ref(v_expr_2778_);
lean_dec_ref(v_e_2687_);
v___x_2787_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2788_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2787_);
v___y_2699_ = v___x_2779_;
v___y_2700_ = v___x_2788_;
goto v___jp_2698_;
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref(v_struct_2690_);
lean_dec_ref(v_e_2687_);
v_a_2789_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2773_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2773_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_del_object(v___x_2747_);
lean_dec(v_a_2725_);
lean_dec(v_a_2723_);
lean_dec_ref(v_struct_2690_);
lean_dec(v_idx_2689_);
lean_dec(v_structName_2688_);
lean_dec_ref(v_e_2687_);
v_a_2798_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2767_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2767_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
v___jp_2806_:
{
lean_object* v_dummy_2813_; lean_object* v_nargs_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_dummy_2813_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2814_ = l_Lean_Expr_getAppNumArgs(v_a_2723_);
lean_inc(v_nargs_2814_);
v___x_2815_ = lean_mk_array(v_nargs_2814_, v_dummy_2813_);
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = lean_nat_sub(v_nargs_2814_, v___x_2816_);
lean_dec(v_nargs_2814_);
lean_inc(v_a_2723_);
v___x_2818_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2723_, v___x_2815_, v___x_2817_);
v___x_2819_ = lean_nat_add(v_numParams_2743_, v_numIndices_2744_);
lean_dec(v_numIndices_2744_);
v___x_2820_ = lean_array_get_size(v___x_2818_);
v___x_2821_ = lean_nat_dec_eq(v___x_2819_, v___x_2820_);
lean_dec(v___x_2819_);
if (v___x_2821_ == 0)
{
if (v___x_2709_ == 0)
{
v___y_2753_ = v___x_2818_;
v___y_2754_ = v___y_2807_;
v___y_2755_ = v___y_2808_;
v___y_2756_ = v___y_2809_;
v___y_2757_ = v___y_2810_;
v___y_2758_ = v___y_2811_;
v___y_2759_ = v___y_2812_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec_ref(v___x_2818_);
lean_dec_ref(v_val_2751_);
lean_del_object(v___x_2747_);
lean_dec(v_numParams_2743_);
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
v___x_2822_ = lean_box(0);
v___x_2823_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2690_, v_structName_2688_, v_idx_2689_, v_a_2723_, lean_box(0), v___x_2822_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
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
else
{
v___y_2753_ = v___x_2818_;
v___y_2754_ = v___y_2807_;
v___y_2755_ = v___y_2808_;
v___y_2756_ = v___y_2809_;
v___y_2757_ = v___y_2810_;
v___y_2758_ = v___y_2811_;
v___y_2759_ = v___y_2812_;
goto v___jp_2752_;
}
}
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec(v_a_2750_);
lean_del_object(v___x_2747_);
lean_dec(v_numIndices_2744_);
lean_dec(v_numParams_2743_);
lean_dec_ref(v_toConstantVal_2742_);
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
v___x_2844_ = lean_box(0);
v___x_2845_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2690_, v_structName_2688_, v_idx_2689_, v_a_2723_, lean_box(0), v___x_2844_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2845_;
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_del_object(v___x_2747_);
lean_dec(v_numIndices_2744_);
lean_dec(v_numParams_2743_);
lean_dec_ref(v_toConstantVal_2742_);
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec(v_a_2723_);
lean_dec_ref(v_struct_2690_);
lean_dec(v_idx_2689_);
lean_dec(v_structName_2688_);
lean_dec_ref(v_e_2687_);
v_a_2846_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2749_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2749_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2740_, 2);
lean_dec_ref(v_val_2739_);
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
goto v___jp_2730_;
}
}
else
{
lean_dec(v_ctors_2740_);
lean_dec_ref(v_val_2739_);
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
goto v___jp_2730_;
}
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_dec(v_val_2738_);
lean_dec(v_us_2728_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
v___x_2856_ = lean_box(0);
v___x_2857_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2690_, v_structName_2688_, v_idx_2689_, v_a_2723_, lean_box(0), v___x_2856_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2857_;
}
}
v___jp_2730_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_box(0);
v___x_2732_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2690_, v_structName_2688_, v_idx_2689_, v_a_2723_, lean_box(0), v___x_2731_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2732_;
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec_ref(v___x_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_e_2687_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2690_, v_structName_2688_, v_idx_2689_, v_a_2723_, lean_box(0), v___x_2858_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2859_;
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_a_2723_);
lean_dec_ref(v_struct_2690_);
lean_dec(v_idx_2689_);
lean_dec(v_structName_2688_);
lean_dec_ref(v_e_2687_);
v_a_2860_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2724_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2724_);
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
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v_struct_2690_);
lean_dec(v_idx_2689_);
lean_dec(v_structName_2688_);
lean_dec_ref(v_e_2687_);
v_a_2868_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2722_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2722_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v_struct_2690_);
lean_dec(v_idx_2689_);
lean_dec(v_structName_2688_);
lean_dec_ref(v_e_2687_);
v_a_2876_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2720_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2720_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
v___jp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___y_2699_);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___y_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
v___jp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___y_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2884_, lean_object* v_structName_2885_, lean_object* v_idx_2886_, lean_object* v_struct_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2884_, v_structName_2885_, v_idx_2886_, v_struct_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec(v_a_2888_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2896_, lean_object* v_struct_2897_, lean_object* v_structName_2898_, uint8_t v_a_2899_, lean_object* v_idx_2900_, lean_object* v_a_2901_, lean_object* v_inst_2902_, lean_object* v_R_2903_, lean_object* v_a_2904_, lean_object* v_b_2905_, lean_object* v_c_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2896_, v_struct_2897_, v_structName_2898_, v_a_2899_, v_idx_2900_, v_a_2901_, v_a_2904_, v_b_2905_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2915_ = _args[0];
lean_object* v_struct_2916_ = _args[1];
lean_object* v_structName_2917_ = _args[2];
lean_object* v_a_2918_ = _args[3];
lean_object* v_idx_2919_ = _args[4];
lean_object* v_a_2920_ = _args[5];
lean_object* v_inst_2921_ = _args[6];
lean_object* v_R_2922_ = _args[7];
lean_object* v_a_2923_ = _args[8];
lean_object* v_b_2924_ = _args[9];
lean_object* v_c_2925_ = _args[10];
lean_object* v___y_2926_ = _args[11];
lean_object* v___y_2927_ = _args[12];
lean_object* v___y_2928_ = _args[13];
lean_object* v___y_2929_ = _args[14];
lean_object* v___y_2930_ = _args[15];
lean_object* v___y_2931_ = _args[16];
lean_object* v___y_2932_ = _args[17];
_start:
{
uint8_t v_a_19705__boxed_2933_; lean_object* v_res_2934_; 
v_a_19705__boxed_2933_ = lean_unbox(v_a_2918_);
v_res_2934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2915_, v_struct_2916_, v_structName_2917_, v_a_19705__boxed_2933_, v_idx_2919_, v_a_2920_, v_inst_2921_, v_R_2922_, v_a_2923_, v_b_2924_, v_c_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec(v_upperBound_2915_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2935_, size_t v_i_2936_, size_t v_stop_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
uint8_t v___x_2945_; 
v___x_2945_ = lean_usize_dec_eq(v_i_2936_, v_stop_2937_);
if (v___x_2945_ == 0)
{
size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2946_ = ((size_t)1ULL);
v___x_2947_ = lean_usize_sub(v_i_2936_, v___x_2946_);
v___x_2948_ = lean_array_uget_borrowed(v_as_2935_, v___x_2947_);
lean_inc(v___x_2948_);
v___x_2949_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2948_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l_Lean_Expr_sortLevel_x21(v_a_2950_);
lean_dec(v_a_2950_);
v___x_2952_ = l_Lean_mkLevelIMax_x27(v___x_2951_, v_b_2938_);
v_i_2936_ = v___x_2947_;
v_b_2938_ = v___x_2952_;
goto _start;
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v_b_2938_);
v_a_2954_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2949_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2949_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_b_2938_);
return v___x_2962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_2963_, lean_object* v_i_2964_, lean_object* v_stop_2965_, lean_object* v_b_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
size_t v_i_boxed_2973_; size_t v_stop_boxed_2974_; lean_object* v_res_2975_; 
v_i_boxed_2973_ = lean_unbox_usize(v_i_2964_);
lean_dec(v_i_2964_);
v_stop_boxed_2974_ = lean_unbox_usize(v_stop_2965_);
lean_dec(v_stop_2965_);
v_res_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_2963_, v_i_boxed_2973_, v_stop_boxed_2974_, v_b_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v_as_2963_);
return v_res_2975_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2979_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_2980_ = lean_unsigned_to_nat(14u);
v___x_2981_ = lean_unsigned_to_nat(22u);
v___x_2982_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_2983_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_2984_ = l_mkPanicMessageWithDecl(v___x_2983_, v___x_2982_, v___x_2981_, v___x_2980_, v___x_2979_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_2985_, lean_object* v_doms_2986_, lean_object* v_body_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_lctx_2995_; lean_object* v_expr_2996_; uint8_t v___x_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v_a_3001_; uint8_t v___x_3006_; 
v_lctx_2995_ = lean_ctor_get(v_a_2990_, 2);
v_expr_2996_ = lean_ctor_get(v_body_2987_, 0);
v___x_2997_ = 1;
v___x_2998_ = 0;
lean_inc_ref(v_lctx_2995_);
v___x_2999_ = l_Lean_LocalContext_mkForall(v_lctx_2995_, v_fvars_2985_, v_expr_2996_, v___x_2997_, v___x_2998_);
v___x_3006_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2988_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3015_; 
v_isSharedCheck_3015_ = !lean_is_exclusive(v_body_2987_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; lean_object* v_unused_3017_; 
v_unused_3016_ = lean_ctor_get(v_body_2987_, 1);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v_body_2987_, 0);
lean_dec(v_unused_3017_);
v___x_3008_ = v_body_2987_;
v_isShared_3009_ = v_isSharedCheck_3015_;
goto v_resetjp_3007_;
}
else
{
lean_dec(v_body_2987_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3015_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = lean_box(0);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_3010_);
lean_ctor_set(v___x_3008_, 0, v___x_2999_);
v___x_3012_ = v___x_3008_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
return v___x_3013_;
}
}
}
else
{
lean_object* v___x_3018_; 
v___x_3018_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___y_3021_; lean_object* v_type_x3f_3038_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v_type_x3f_3038_ = lean_ctor_get(v_a_3019_, 1);
lean_inc(v_type_x3f_3038_);
lean_dec(v_a_3019_);
if (lean_obj_tag(v_type_x3f_3038_) == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3040_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3039_);
v___y_3021_ = v___x_3040_;
goto v___jp_3020_;
}
else
{
lean_object* v_val_3041_; 
v_val_3041_ = lean_ctor_get(v_type_x3f_3038_, 0);
lean_inc(v_val_3041_);
lean_dec_ref_known(v_type_x3f_3038_, 1);
v___y_3021_ = v_val_3041_;
goto v___jp_3020_;
}
v___jp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3022_ = l_Lean_Expr_sortLevel_x21(v___y_3021_);
lean_dec_ref(v___y_3021_);
v___x_3023_ = lean_array_get_size(v_doms_2986_);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = lean_nat_dec_lt(v___x_3024_, v___x_3023_);
if (v___x_3025_ == 0)
{
v_a_3001_ = v___x_3022_;
goto v___jp_3000_;
}
else
{
size_t v___x_3026_; size_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = lean_usize_of_nat(v___x_3023_);
v___x_3027_ = ((size_t)0ULL);
v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_2986_, v___x_3026_, v___x_3027_, v___x_3022_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v_a_3001_ = v_a_3029_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v___x_2999_);
v_a_3030_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3028_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3028_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2999_);
return v___x_3018_;
}
}
v___jp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3002_ = l_Lean_Expr_sort___override(v_a_3001_);
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_2999_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3042_, lean_object* v_doms_3043_, lean_object* v_body_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3042_, v_doms_3043_, v_body_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_doms_3043_);
lean_dec_ref(v_fvars_3042_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3053_, size_t v_i_3054_, size_t v_stop_3055_, lean_object* v_b_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3053_, v_i_3054_, v_stop_3055_, v_b_3056_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3065_, lean_object* v_i_3066_, lean_object* v_stop_3067_, lean_object* v_b_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
size_t v_i_boxed_3076_; size_t v_stop_boxed_3077_; lean_object* v_res_3078_; 
v_i_boxed_3076_ = lean_unbox_usize(v_i_3066_);
lean_dec(v_i_3066_);
v_stop_boxed_3077_ = lean_unbox_usize(v_stop_3067_);
lean_dec(v_stop_3067_);
v_res_3078_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3065_, v_i_boxed_3076_, v_stop_boxed_3077_, v_b_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v_as_3065_);
return v_res_3078_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3079_, lean_object* v_opt_3080_){
_start:
{
lean_object* v_name_3081_; lean_object* v_defValue_3082_; lean_object* v_map_3083_; lean_object* v___x_3084_; 
v_name_3081_ = lean_ctor_get(v_opt_3080_, 0);
v_defValue_3082_ = lean_ctor_get(v_opt_3080_, 1);
v_map_3083_ = lean_ctor_get(v_opts_3079_, 0);
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3083_, v_name_3081_);
if (lean_obj_tag(v___x_3084_) == 0)
{
uint8_t v___x_3085_; 
v___x_3085_ = lean_unbox(v_defValue_3082_);
return v___x_3085_;
}
else
{
lean_object* v_val_3086_; 
v_val_3086_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_val_3086_);
lean_dec_ref_known(v___x_3084_, 1);
if (lean_obj_tag(v_val_3086_) == 1)
{
uint8_t v_v_3087_; 
v_v_3087_ = lean_ctor_get_uint8(v_val_3086_, 0);
lean_dec_ref_known(v_val_3086_, 0);
return v_v_3087_;
}
else
{
uint8_t v___x_3088_; 
lean_dec(v_val_3086_);
v___x_3088_ = lean_unbox(v_defValue_3082_);
return v___x_3088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3089_, lean_object* v_opt_3090_){
_start:
{
uint8_t v_res_3091_; lean_object* v_r_3092_; 
v_res_3091_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3089_, v_opt_3090_);
lean_dec_ref(v_opt_3090_);
lean_dec_ref(v_opts_3089_);
v_r_3092_ = lean_box(v_res_3091_);
return v_r_3092_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3093_){
_start:
{
if (lean_obj_tag(v_x_3093_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
v_a_3095_ = lean_ctor_get(v_x_3093_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_x_3093_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v_x_3093_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v_x_3093_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 1);
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_a_3103_ = lean_ctor_get(v_x_3093_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_x_3093_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v_x_3093_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v_x_3093_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 0);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3114_){
_start:
{
if (lean_obj_tag(v_e_3114_) == 0)
{
uint8_t v___x_3115_; 
v___x_3115_ = 2;
return v___x_3115_;
}
else
{
uint8_t v___x_3116_; 
v___x_3116_ = 0;
return v___x_3116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3117_){
_start:
{
uint8_t v_res_3118_; lean_object* v_r_3119_; 
v_res_3118_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3117_);
lean_dec_ref(v_e_3117_);
v_r_3119_ = lean_box(v_res_3118_);
return v_r_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3120_, lean_object* v_opt_3121_){
_start:
{
lean_object* v_name_3122_; lean_object* v_defValue_3123_; lean_object* v_map_3124_; lean_object* v___x_3125_; 
v_name_3122_ = lean_ctor_get(v_opt_3121_, 0);
v_defValue_3123_ = lean_ctor_get(v_opt_3121_, 1);
v_map_3124_ = lean_ctor_get(v_opts_3120_, 0);
v___x_3125_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3124_, v_name_3122_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_inc(v_defValue_3123_);
return v_defValue_3123_;
}
else
{
lean_object* v_val_3126_; 
v_val_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3125_, 1);
if (lean_obj_tag(v_val_3126_) == 3)
{
lean_object* v_v_3127_; 
v_v_3127_ = lean_ctor_get(v_val_3126_, 0);
lean_inc(v_v_3127_);
lean_dec_ref_known(v_val_3126_, 1);
return v_v_3127_;
}
else
{
lean_dec(v_val_3126_);
lean_inc(v_defValue_3123_);
return v_defValue_3123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3128_, lean_object* v_opt_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3128_, v_opt_3129_);
lean_dec_ref(v_opt_3129_);
lean_dec_ref(v_opts_3128_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3131_, size_t v_i_3132_, lean_object* v_bs_3133_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_usize_dec_lt(v_i_3132_, v_sz_3131_);
if (v___x_3134_ == 0)
{
return v_bs_3133_;
}
else
{
lean_object* v_v_3135_; lean_object* v_msg_3136_; lean_object* v___x_3137_; lean_object* v_bs_x27_3138_; size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v_v_3135_ = lean_array_uget_borrowed(v_bs_3133_, v_i_3132_);
v_msg_3136_ = lean_ctor_get(v_v_3135_, 1);
lean_inc_ref(v_msg_3136_);
v___x_3137_ = lean_unsigned_to_nat(0u);
v_bs_x27_3138_ = lean_array_uset(v_bs_3133_, v_i_3132_, v___x_3137_);
v___x_3139_ = ((size_t)1ULL);
v___x_3140_ = lean_usize_add(v_i_3132_, v___x_3139_);
v___x_3141_ = lean_array_uset(v_bs_x27_3138_, v_i_3132_, v_msg_3136_);
v_i_3132_ = v___x_3140_;
v_bs_3133_ = v___x_3141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3143_, lean_object* v_i_3144_, lean_object* v_bs_3145_){
_start:
{
size_t v_sz_boxed_3146_; size_t v_i_boxed_3147_; lean_object* v_res_3148_; 
v_sz_boxed_3146_ = lean_unbox_usize(v_sz_3143_);
lean_dec(v_sz_3143_);
v_i_boxed_3147_ = lean_unbox_usize(v_i_3144_);
lean_dec(v_i_3144_);
v_res_3148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3146_, v_i_boxed_3147_, v_bs_3145_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3149_, lean_object* v_data_3150_, lean_object* v_ref_3151_, lean_object* v_msg_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_toCold_3158_; lean_object* v_currRecDepth_3159_; lean_object* v_ref_3160_; uint8_t v_diag_3161_; uint8_t v_suppressElabErrors_3162_; lean_object* v___x_3163_; lean_object* v_traceState_3164_; lean_object* v_traces_3165_; lean_object* v_ref_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; size_t v_sz_3169_; size_t v___x_3170_; lean_object* v___x_3171_; lean_object* v_msg_3172_; lean_object* v___x_3173_; lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3211_; 
v_toCold_3158_ = lean_ctor_get(v___y_3155_, 0);
v_currRecDepth_3159_ = lean_ctor_get(v___y_3155_, 1);
v_ref_3160_ = lean_ctor_get(v___y_3155_, 2);
v_diag_3161_ = lean_ctor_get_uint8(v___y_3155_, sizeof(void*)*3);
v_suppressElabErrors_3162_ = lean_ctor_get_uint8(v___y_3155_, sizeof(void*)*3 + 1);
v___x_3163_ = lean_st_ref_get(v___y_3156_);
v_traceState_3164_ = lean_ctor_get(v___x_3163_, 4);
lean_inc_ref(v_traceState_3164_);
lean_dec(v___x_3163_);
v_traces_3165_ = lean_ctor_get(v_traceState_3164_, 0);
lean_inc_ref(v_traces_3165_);
lean_dec_ref(v_traceState_3164_);
v_ref_3166_ = l_Lean_replaceRef(v_ref_3151_, v_ref_3160_);
lean_inc(v_currRecDepth_3159_);
lean_inc_ref(v_toCold_3158_);
v___x_3167_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3167_, 0, v_toCold_3158_);
lean_ctor_set(v___x_3167_, 1, v_currRecDepth_3159_);
lean_ctor_set(v___x_3167_, 2, v_ref_3166_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*3, v_diag_3161_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*3 + 1, v_suppressElabErrors_3162_);
v___x_3168_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3165_);
lean_dec_ref(v_traces_3165_);
v_sz_3169_ = lean_array_size(v___x_3168_);
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3169_, v___x_3170_, v___x_3168_);
v_msg_3172_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3172_, 0, v_data_3150_);
lean_ctor_set(v_msg_3172_, 1, v_msg_3152_);
lean_ctor_set(v_msg_3172_, 2, v___x_3171_);
v___x_3173_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3172_, v___y_3153_, v___y_3154_, v___x_3167_, v___y_3156_);
lean_dec_ref_known(v___x_3167_, 3);
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3211_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3211_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; lean_object* v_traceState_3179_; lean_object* v_env_3180_; lean_object* v_nextMacroScope_3181_; lean_object* v_ngen_3182_; lean_object* v_auxDeclNGen_3183_; lean_object* v_cache_3184_; lean_object* v_messages_3185_; lean_object* v_infoState_3186_; lean_object* v_snapshotTasks_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3210_; 
v___x_3178_ = lean_st_ref_take(v___y_3156_);
v_traceState_3179_ = lean_ctor_get(v___x_3178_, 4);
v_env_3180_ = lean_ctor_get(v___x_3178_, 0);
v_nextMacroScope_3181_ = lean_ctor_get(v___x_3178_, 1);
v_ngen_3182_ = lean_ctor_get(v___x_3178_, 2);
v_auxDeclNGen_3183_ = lean_ctor_get(v___x_3178_, 3);
v_cache_3184_ = lean_ctor_get(v___x_3178_, 5);
v_messages_3185_ = lean_ctor_get(v___x_3178_, 6);
v_infoState_3186_ = lean_ctor_get(v___x_3178_, 7);
v_snapshotTasks_3187_ = lean_ctor_get(v___x_3178_, 8);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3189_ = v___x_3178_;
v_isShared_3190_ = v_isSharedCheck_3210_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_snapshotTasks_3187_);
lean_inc(v_infoState_3186_);
lean_inc(v_messages_3185_);
lean_inc(v_cache_3184_);
lean_inc(v_traceState_3179_);
lean_inc(v_auxDeclNGen_3183_);
lean_inc(v_ngen_3182_);
lean_inc(v_nextMacroScope_3181_);
lean_inc(v_env_3180_);
lean_dec(v___x_3178_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3210_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
uint64_t v_tid_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3208_; 
v_tid_3191_ = lean_ctor_get_uint64(v_traceState_3179_, sizeof(void*)*1);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_traceState_3179_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_traceState_3179_, 0);
lean_dec(v_unused_3209_);
v___x_3193_ = v_traceState_3179_;
v_isShared_3194_ = v_isSharedCheck_3208_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_traceState_3179_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3208_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v_ref_3151_);
lean_ctor_set(v___x_3195_, 1, v_a_3174_);
v___x_3196_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3149_, v___x_3195_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3196_);
v___x_3198_ = v___x_3193_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3196_);
lean_ctor_set_uint64(v_reuseFailAlloc_3207_, sizeof(void*)*1, v_tid_3191_);
v___x_3198_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3200_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 4, v___x_3198_);
v___x_3200_ = v___x_3189_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_env_3180_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_nextMacroScope_3181_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_ngen_3182_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v_auxDeclNGen_3183_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3206_, 5, v_cache_3184_);
lean_ctor_set(v_reuseFailAlloc_3206_, 6, v_messages_3185_);
lean_ctor_set(v_reuseFailAlloc_3206_, 7, v_infoState_3186_);
lean_ctor_set(v_reuseFailAlloc_3206_, 8, v_snapshotTasks_3187_);
v___x_3200_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3201_ = lean_st_ref_put(v___y_3156_, v___x_3200_);
v___x_3202_ = lean_box(0);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 0, v___x_3202_);
v___x_3204_ = v___x_3176_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3212_, lean_object* v_data_3213_, lean_object* v_ref_3214_, lean_object* v_msg_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3212_, v_data_3213_, v_ref_3214_, v_msg_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
return v_res_3221_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3224_ = l_Lean_stringToMessageData(v___x_3223_);
return v___x_3224_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3225_; double v___x_3226_; 
v___x_3225_ = lean_unsigned_to_nat(1000u);
v___x_3226_ = lean_float_of_nat(v___x_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3227_, uint8_t v_collapsed_3228_, lean_object* v_tag_3229_, lean_object* v_opts_3230_, uint8_t v_clsEnabled_3231_, lean_object* v_oldTraces_3232_, lean_object* v_msg_3233_, lean_object* v_resStartStop_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_fst_3242_; lean_object* v_snd_3243_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v_data_3247_; lean_object* v_fst_3258_; lean_object* v_snd_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; lean_object* v___y_3263_; lean_object* v_a_3264_; uint8_t v___y_3279_; double v___y_3310_; 
v_fst_3242_ = lean_ctor_get(v_resStartStop_3234_, 0);
lean_inc(v_fst_3242_);
v_snd_3243_ = lean_ctor_get(v_resStartStop_3234_, 1);
lean_inc(v_snd_3243_);
lean_dec_ref(v_resStartStop_3234_);
v_fst_3258_ = lean_ctor_get(v_snd_3243_, 0);
lean_inc(v_fst_3258_);
v_snd_3259_ = lean_ctor_get(v_snd_3243_, 1);
lean_inc(v_snd_3259_);
lean_dec(v_snd_3243_);
v___x_3260_ = l_Lean_trace_profiler;
v___x_3261_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3230_, v___x_3260_);
if (v___x_3261_ == 0)
{
v___y_3279_ = v___x_3261_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3316_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3230_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; double v___x_3319_; double v___x_3320_; double v___x_3321_; 
v___x_3317_ = l_Lean_trace_profiler_threshold;
v___x_3318_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3230_, v___x_3317_);
v___x_3319_ = lean_float_of_nat(v___x_3318_);
v___x_3320_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3321_ = lean_float_div(v___x_3319_, v___x_3320_);
v___y_3310_ = v___x_3321_;
goto v___jp_3309_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; double v___x_3324_; 
v___x_3322_ = l_Lean_trace_profiler_threshold;
v___x_3323_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3230_, v___x_3322_);
v___x_3324_ = lean_float_of_nat(v___x_3323_);
v___y_3310_ = v___x_3324_;
goto v___jp_3309_;
}
}
v___jp_3244_:
{
lean_object* v___x_3248_; 
lean_inc(v___y_3246_);
v___x_3248_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3232_, v_data_3247_, v___y_3246_, v___y_3245_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v___x_3249_; 
lean_dec_ref_known(v___x_3248_, 1);
v___x_3249_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3242_);
return v___x_3249_;
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v_fst_3242_);
v_a_3250_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3248_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3248_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
v___jp_3262_:
{
uint8_t v_result_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; double v___x_3268_; lean_object* v_data_3269_; 
v_result_3265_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3242_);
v___x_3266_ = lean_box(v_result_3265_);
v___x_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
v___x_3268_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3229_);
lean_inc_ref(v___x_3267_);
lean_inc(v_cls_3227_);
v_data_3269_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3269_, 0, v_cls_3227_);
lean_ctor_set(v_data_3269_, 1, v___x_3267_);
lean_ctor_set(v_data_3269_, 2, v_tag_3229_);
lean_ctor_set_float(v_data_3269_, sizeof(void*)*3, v___x_3268_);
lean_ctor_set_float(v_data_3269_, sizeof(void*)*3 + 8, v___x_3268_);
lean_ctor_set_uint8(v_data_3269_, sizeof(void*)*3 + 16, v_collapsed_3228_);
if (v___x_3261_ == 0)
{
lean_dec_ref_known(v___x_3267_, 1);
lean_dec(v_snd_3259_);
lean_dec(v_fst_3258_);
lean_dec_ref(v_tag_3229_);
lean_dec(v_cls_3227_);
v___y_3245_ = v_a_3264_;
v___y_3246_ = v___y_3263_;
v_data_3247_ = v_data_3269_;
goto v___jp_3244_;
}
else
{
lean_object* v_data_3270_; double v___x_3271_; double v___x_3272_; 
lean_dec_ref_known(v_data_3269_, 3);
v_data_3270_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3270_, 0, v_cls_3227_);
lean_ctor_set(v_data_3270_, 1, v___x_3267_);
lean_ctor_set(v_data_3270_, 2, v_tag_3229_);
v___x_3271_ = lean_unbox_float(v_fst_3258_);
lean_dec(v_fst_3258_);
lean_ctor_set_float(v_data_3270_, sizeof(void*)*3, v___x_3271_);
v___x_3272_ = lean_unbox_float(v_snd_3259_);
lean_dec(v_snd_3259_);
lean_ctor_set_float(v_data_3270_, sizeof(void*)*3 + 8, v___x_3272_);
lean_ctor_set_uint8(v_data_3270_, sizeof(void*)*3 + 16, v_collapsed_3228_);
v___y_3245_ = v_a_3264_;
v___y_3246_ = v___y_3263_;
v_data_3247_ = v_data_3270_;
goto v___jp_3244_;
}
}
v___jp_3273_:
{
lean_object* v_ref_3274_; lean_object* v___x_3275_; 
v_ref_3274_ = lean_ctor_get(v___y_3239_, 2);
lean_inc(v___y_3240_);
lean_inc_ref(v___y_3239_);
lean_inc(v___y_3238_);
lean_inc_ref(v___y_3237_);
lean_inc(v___y_3236_);
lean_inc(v___y_3235_);
lean_inc(v_fst_3242_);
v___x_3275_ = lean_apply_8(v_msg_3233_, v_fst_3242_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, lean_box(0));
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v___y_3263_ = v_ref_3274_;
v_a_3264_ = v_a_3276_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3277_; 
lean_dec_ref_known(v___x_3275_, 1);
v___x_3277_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3263_ = v_ref_3274_;
v_a_3264_ = v___x_3277_;
goto v___jp_3262_;
}
}
v___jp_3278_:
{
if (v_clsEnabled_3231_ == 0)
{
if (v___y_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v_traceState_3281_; lean_object* v_env_3282_; lean_object* v_nextMacroScope_3283_; lean_object* v_ngen_3284_; lean_object* v_auxDeclNGen_3285_; lean_object* v_cache_3286_; lean_object* v_messages_3287_; lean_object* v_infoState_3288_; lean_object* v_snapshotTasks_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v_snd_3259_);
lean_dec(v_fst_3258_);
lean_dec_ref(v_msg_3233_);
lean_dec_ref(v_tag_3229_);
lean_dec(v_cls_3227_);
v___x_3280_ = lean_st_ref_take(v___y_3240_);
v_traceState_3281_ = lean_ctor_get(v___x_3280_, 4);
v_env_3282_ = lean_ctor_get(v___x_3280_, 0);
v_nextMacroScope_3283_ = lean_ctor_get(v___x_3280_, 1);
v_ngen_3284_ = lean_ctor_get(v___x_3280_, 2);
v_auxDeclNGen_3285_ = lean_ctor_get(v___x_3280_, 3);
v_cache_3286_ = lean_ctor_get(v___x_3280_, 5);
v_messages_3287_ = lean_ctor_get(v___x_3280_, 6);
v_infoState_3288_ = lean_ctor_get(v___x_3280_, 7);
v_snapshotTasks_3289_ = lean_ctor_get(v___x_3280_, 8);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3291_ = v___x_3280_;
v_isShared_3292_ = v_isSharedCheck_3308_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_snapshotTasks_3289_);
lean_inc(v_infoState_3288_);
lean_inc(v_messages_3287_);
lean_inc(v_cache_3286_);
lean_inc(v_traceState_3281_);
lean_inc(v_auxDeclNGen_3285_);
lean_inc(v_ngen_3284_);
lean_inc(v_nextMacroScope_3283_);
lean_inc(v_env_3282_);
lean_dec(v___x_3280_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3308_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
uint64_t v_tid_3293_; lean_object* v_traces_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3307_; 
v_tid_3293_ = lean_ctor_get_uint64(v_traceState_3281_, sizeof(void*)*1);
v_traces_3294_ = lean_ctor_get(v_traceState_3281_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_traceState_3281_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3296_ = v_traceState_3281_;
v_isShared_3297_ = v_isSharedCheck_3307_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_traces_3294_);
lean_dec(v_traceState_3281_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3307_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3298_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3232_, v_traces_3294_);
lean_dec_ref(v_traces_3294_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v___x_3298_);
v___x_3300_ = v___x_3296_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3298_);
lean_ctor_set_uint64(v_reuseFailAlloc_3306_, sizeof(void*)*1, v_tid_3293_);
v___x_3300_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3302_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 4, v___x_3300_);
v___x_3302_ = v___x_3291_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_env_3282_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_nextMacroScope_3283_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_ngen_3284_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_auxDeclNGen_3285_);
lean_ctor_set(v_reuseFailAlloc_3305_, 4, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3305_, 5, v_cache_3286_);
lean_ctor_set(v_reuseFailAlloc_3305_, 6, v_messages_3287_);
lean_ctor_set(v_reuseFailAlloc_3305_, 7, v_infoState_3288_);
lean_ctor_set(v_reuseFailAlloc_3305_, 8, v_snapshotTasks_3289_);
v___x_3302_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_st_ref_put(v___y_3240_, v___x_3302_);
v___x_3304_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3242_);
return v___x_3304_;
}
}
}
}
}
else
{
goto v___jp_3273_;
}
}
else
{
goto v___jp_3273_;
}
}
v___jp_3309_:
{
double v___x_3311_; double v___x_3312_; double v___x_3313_; uint8_t v___x_3314_; 
v___x_3311_ = lean_unbox_float(v_snd_3259_);
v___x_3312_ = lean_unbox_float(v_fst_3258_);
v___x_3313_ = lean_float_sub(v___x_3311_, v___x_3312_);
v___x_3314_ = lean_float_decLt(v___y_3310_, v___x_3313_);
v___y_3279_ = v___x_3314_;
goto v___jp_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3325_, lean_object* v_collapsed_3326_, lean_object* v_tag_3327_, lean_object* v_opts_3328_, lean_object* v_clsEnabled_3329_, lean_object* v_oldTraces_3330_, lean_object* v_msg_3331_, lean_object* v_resStartStop_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v_collapsed_boxed_3340_; uint8_t v_clsEnabled_boxed_3341_; lean_object* v_res_3342_; 
v_collapsed_boxed_3340_ = lean_unbox(v_collapsed_3326_);
v_clsEnabled_boxed_3341_ = lean_unbox(v_clsEnabled_3329_);
v_res_3342_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3325_, v_collapsed_boxed_3340_, v_tag_3327_, v_opts_3328_, v_clsEnabled_boxed_3341_, v_oldTraces_3330_, v_msg_3331_, v_resStartStop_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v_opts_3328_);
return v_res_3342_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = lean_unsigned_to_nat(32u);
v___x_3344_ = lean_mk_empty_array_with_capacity(v___x_3343_);
v___x_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
return v___x_3345_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3346_ = ((size_t)5ULL);
v___x_3347_ = lean_unsigned_to_nat(0u);
v___x_3348_ = lean_unsigned_to_nat(32u);
v___x_3349_ = lean_mk_empty_array_with_capacity(v___x_3348_);
v___x_3350_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3351_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___x_3349_);
lean_ctor_set(v___x_3351_, 2, v___x_3347_);
lean_ctor_set(v___x_3351_, 3, v___x_3347_);
lean_ctor_set_usize(v___x_3351_, 4, v___x_3346_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v_traceState_3355_; lean_object* v_traces_3356_; lean_object* v___x_3357_; lean_object* v_traceState_3358_; lean_object* v_env_3359_; lean_object* v_nextMacroScope_3360_; lean_object* v_ngen_3361_; lean_object* v_auxDeclNGen_3362_; lean_object* v_cache_3363_; lean_object* v_messages_3364_; lean_object* v_infoState_3365_; lean_object* v_snapshotTasks_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3385_; 
v___x_3354_ = lean_st_ref_get(v___y_3352_);
v_traceState_3355_ = lean_ctor_get(v___x_3354_, 4);
lean_inc_ref(v_traceState_3355_);
lean_dec(v___x_3354_);
v_traces_3356_ = lean_ctor_get(v_traceState_3355_, 0);
lean_inc_ref(v_traces_3356_);
lean_dec_ref(v_traceState_3355_);
v___x_3357_ = lean_st_ref_take(v___y_3352_);
v_traceState_3358_ = lean_ctor_get(v___x_3357_, 4);
v_env_3359_ = lean_ctor_get(v___x_3357_, 0);
v_nextMacroScope_3360_ = lean_ctor_get(v___x_3357_, 1);
v_ngen_3361_ = lean_ctor_get(v___x_3357_, 2);
v_auxDeclNGen_3362_ = lean_ctor_get(v___x_3357_, 3);
v_cache_3363_ = lean_ctor_get(v___x_3357_, 5);
v_messages_3364_ = lean_ctor_get(v___x_3357_, 6);
v_infoState_3365_ = lean_ctor_get(v___x_3357_, 7);
v_snapshotTasks_3366_ = lean_ctor_get(v___x_3357_, 8);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3368_ = v___x_3357_;
v_isShared_3369_ = v_isSharedCheck_3385_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_snapshotTasks_3366_);
lean_inc(v_infoState_3365_);
lean_inc(v_messages_3364_);
lean_inc(v_cache_3363_);
lean_inc(v_traceState_3358_);
lean_inc(v_auxDeclNGen_3362_);
lean_inc(v_ngen_3361_);
lean_inc(v_nextMacroScope_3360_);
lean_inc(v_env_3359_);
lean_dec(v___x_3357_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3385_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
uint64_t v_tid_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3383_; 
v_tid_3370_ = lean_ctor_get_uint64(v_traceState_3358_, sizeof(void*)*1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_traceState_3358_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; 
v_unused_3384_ = lean_ctor_get(v_traceState_3358_, 0);
lean_dec(v_unused_3384_);
v___x_3372_ = v_traceState_3358_;
v_isShared_3373_ = v_isSharedCheck_3383_;
goto v_resetjp_3371_;
}
else
{
lean_dec(v_traceState_3358_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3383_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3374_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3374_);
v___x_3376_ = v___x_3372_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3374_);
lean_ctor_set_uint64(v_reuseFailAlloc_3382_, sizeof(void*)*1, v_tid_3370_);
v___x_3376_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v___x_3376_);
v___x_3378_ = v___x_3368_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_env_3359_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_nextMacroScope_3360_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_ngen_3361_);
lean_ctor_set(v_reuseFailAlloc_3381_, 3, v_auxDeclNGen_3362_);
lean_ctor_set(v_reuseFailAlloc_3381_, 4, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3381_, 5, v_cache_3363_);
lean_ctor_set(v_reuseFailAlloc_3381_, 6, v_messages_3364_);
lean_ctor_set(v_reuseFailAlloc_3381_, 7, v_infoState_3365_);
lean_ctor_set(v_reuseFailAlloc_3381_, 8, v_snapshotTasks_3366_);
v___x_3378_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_st_ref_put(v___y_3352_, v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v_traces_3356_);
return v___x_3380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3386_);
lean_dec(v___y_3386_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v___x_3397_; 
lean_inc(v___y_3391_);
lean_inc(v___y_3390_);
v___x_3397_ = lean_apply_7(v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, lean_box(0));
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3407_, lean_object* v_localInsts_3408_, lean_object* v_x_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___f_3417_; lean_object* v___x_3418_; 
lean_inc(v___y_3411_);
lean_inc(v___y_3410_);
v___f_3417_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3417_, 0, v_x_3409_);
lean_closure_set(v___f_3417_, 1, v___y_3410_);
lean_closure_set(v___f_3417_, 2, v___y_3411_);
v___x_3418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3407_, v_localInsts_3408_, v___f_3417_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3418_) == 0)
{
return v___x_3418_;
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3427_, lean_object* v_localInsts_3428_, lean_object* v_x_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3427_, v_localInsts_3428_, v_x_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec(v___y_3430_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; lean_object* v_ngen_3441_; lean_object* v_namePrefix_3442_; lean_object* v_idx_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3472_; 
v___x_3440_ = lean_st_ref_get(v___y_3438_);
v_ngen_3441_ = lean_ctor_get(v___x_3440_, 2);
lean_inc_ref(v_ngen_3441_);
lean_dec(v___x_3440_);
v_namePrefix_3442_ = lean_ctor_get(v_ngen_3441_, 0);
v_idx_3443_ = lean_ctor_get(v_ngen_3441_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_ngen_3441_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3445_ = v_ngen_3441_;
v_isShared_3446_ = v_isSharedCheck_3472_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_idx_3443_);
lean_inc(v_namePrefix_3442_);
lean_dec(v_ngen_3441_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3472_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v_env_3448_; lean_object* v_nextMacroScope_3449_; lean_object* v_auxDeclNGen_3450_; lean_object* v_traceState_3451_; lean_object* v_cache_3452_; lean_object* v_messages_3453_; lean_object* v_infoState_3454_; lean_object* v_snapshotTasks_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3470_; 
v___x_3447_ = lean_st_ref_take(v___y_3438_);
v_env_3448_ = lean_ctor_get(v___x_3447_, 0);
v_nextMacroScope_3449_ = lean_ctor_get(v___x_3447_, 1);
v_auxDeclNGen_3450_ = lean_ctor_get(v___x_3447_, 3);
v_traceState_3451_ = lean_ctor_get(v___x_3447_, 4);
v_cache_3452_ = lean_ctor_get(v___x_3447_, 5);
v_messages_3453_ = lean_ctor_get(v___x_3447_, 6);
v_infoState_3454_ = lean_ctor_get(v___x_3447_, 7);
v_snapshotTasks_3455_ = lean_ctor_get(v___x_3447_, 8);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v___x_3447_, 2);
lean_dec(v_unused_3471_);
v___x_3457_ = v___x_3447_;
v_isShared_3458_ = v_isSharedCheck_3470_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_snapshotTasks_3455_);
lean_inc(v_infoState_3454_);
lean_inc(v_messages_3453_);
lean_inc(v_cache_3452_);
lean_inc(v_traceState_3451_);
lean_inc(v_auxDeclNGen_3450_);
lean_inc(v_nextMacroScope_3449_);
lean_inc(v_env_3448_);
lean_dec(v___x_3447_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3470_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_r_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
lean_inc(v_idx_3443_);
lean_inc(v_namePrefix_3442_);
v_r_3459_ = l_Lean_Name_num___override(v_namePrefix_3442_, v_idx_3443_);
v___x_3460_ = lean_unsigned_to_nat(1u);
v___x_3461_ = lean_nat_add(v_idx_3443_, v___x_3460_);
lean_dec(v_idx_3443_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v___x_3461_);
v___x_3463_ = v___x_3445_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_namePrefix_3442_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 2, v___x_3463_);
v___x_3465_ = v___x_3457_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_env_3448_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_nextMacroScope_3449_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_auxDeclNGen_3450_);
lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_traceState_3451_);
lean_ctor_set(v_reuseFailAlloc_3468_, 5, v_cache_3452_);
lean_ctor_set(v_reuseFailAlloc_3468_, 6, v_messages_3453_);
lean_ctor_set(v_reuseFailAlloc_3468_, 7, v_infoState_3454_);
lean_ctor_set(v_reuseFailAlloc_3468_, 8, v_snapshotTasks_3455_);
v___x_3465_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_st_ref_put(v___y_3438_, v___x_3465_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_r_3459_);
return v___x_3467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3473_);
lean_dec(v___y_3473_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___x_3483_; lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v___x_3483_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3481_);
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec(v___y_3492_);
return v_res_3499_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3502_ = l_Lean_stringToMessageData(v___x_3501_);
return v___x_3502_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3505_ = l_Lean_stringToMessageData(v___x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3508_, lean_object* v_x_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___y_3519_; uint8_t v___x_3528_; 
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3528_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3510_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; 
v___x_3529_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3519_ = v___x_3529_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3530_; 
v___x_3530_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3519_ = v___x_3530_;
goto v___jp_3518_;
}
v___jp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_inc_ref(v___y_3519_);
v___x_3520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3520_, 0, v___y_3519_);
v___x_3521_ = l_Lean_MessageData_ofFormat(v___x_3520_);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3517_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_indentExpr(v_e_3508_);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
return v___x_3527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3531_, lean_object* v_x_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3531_, v_x_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v_x_3532_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3541_, lean_object* v_x_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_keyedConfig_3550_; uint8_t v_trackZetaDelta_3551_; lean_object* v_zetaDeltaSet_3552_; lean_object* v_localInstances_3553_; lean_object* v_defEqCtx_x3f_3554_; lean_object* v_synthPendingDepth_3555_; lean_object* v_customCanUnfoldPredicate_x3f_3556_; uint8_t v_univApprox_3557_; uint8_t v_inTypeClassResolution_3558_; uint8_t v_cacheInferType_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_keyedConfig_3550_ = lean_ctor_get(v___y_3545_, 0);
v_trackZetaDelta_3551_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7);
v_zetaDeltaSet_3552_ = lean_ctor_get(v___y_3545_, 1);
v_localInstances_3553_ = lean_ctor_get(v___y_3545_, 3);
v_defEqCtx_x3f_3554_ = lean_ctor_get(v___y_3545_, 4);
v_synthPendingDepth_3555_ = lean_ctor_get(v___y_3545_, 5);
v_customCanUnfoldPredicate_x3f_3556_ = lean_ctor_get(v___y_3545_, 6);
v_univApprox_3557_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3558_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7 + 2);
v_cacheInferType_3559_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3556_);
lean_inc(v_synthPendingDepth_3555_);
lean_inc(v_defEqCtx_x3f_3554_);
lean_inc_ref(v_localInstances_3553_);
lean_inc(v_zetaDeltaSet_3552_);
lean_inc_ref(v_keyedConfig_3550_);
v___x_3560_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3560_, 0, v_keyedConfig_3550_);
lean_ctor_set(v___x_3560_, 1, v_zetaDeltaSet_3552_);
lean_ctor_set(v___x_3560_, 2, v_lctx_3541_);
lean_ctor_set(v___x_3560_, 3, v_localInstances_3553_);
lean_ctor_set(v___x_3560_, 4, v_defEqCtx_x3f_3554_);
lean_ctor_set(v___x_3560_, 5, v_synthPendingDepth_3555_);
lean_ctor_set(v___x_3560_, 6, v_customCanUnfoldPredicate_x3f_3556_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*7, v_trackZetaDelta_3551_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*7 + 1, v_univApprox_3557_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3558_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*7 + 3, v_cacheInferType_3559_);
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v___y_3546_);
lean_inc(v___y_3544_);
lean_inc(v___y_3543_);
v___x_3561_ = lean_apply_7(v_x_3542_, v___y_3543_, v___y_3544_, v___x_3560_, v___y_3546_, v___y_3547_, v___y_3548_, lean_box(0));
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
else
{
return v___x_3561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3570_, v_x_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec(v___y_3572_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3582_, lean_object* v_letFVars_3583_, lean_object* v_lctx_3584_, lean_object* v_v_3585_, lean_object* v_e_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3594_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3595_ = lean_expr_instantiate_rev(v_e_3586_, v_fvars_3582_);
v___x_3596_ = lean_apply_1(v_v_3585_, v___x_3595_);
v___x_3597_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3597_, 0, lean_box(0));
lean_closure_set(v___x_3597_, 1, v_letFVars_3583_);
lean_closure_set(v___x_3597_, 2, v___x_3596_);
v___x_3598_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3584_, v___x_3594_, v___x_3597_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3599_, lean_object* v_letFVars_3600_, lean_object* v_lctx_3601_, lean_object* v_v_3602_, lean_object* v_e_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3599_, v_letFVars_3600_, v_lctx_3601_, v_v_3602_, v_e_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v_e_3603_);
lean_dec_ref(v_fvars_3599_);
return v_res_3611_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3614_ = l_Lean_stringToMessageData(v___x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
lean_inc_ref(v_a_3615_);
v___x_3624_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3615_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v_expr_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3676_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v_expr_3626_ = lean_ctor_get(v_a_3616_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_a_3616_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v_a_3616_, 1);
lean_dec(v_unused_3677_);
v___x_3628_ = v_a_3616_;
v_isShared_3629_ = v_isSharedCheck_3676_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_expr_3626_);
lean_dec(v_a_3616_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3676_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; 
lean_inc(v_a_3625_);
lean_inc_ref(v_expr_3626_);
v___x_3630_ = l_Lean_Meta_isExprDefEq(v_expr_3626_, v_a_3625_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3667_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3667_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3667_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_unbox(v_a_3631_);
lean_dec(v_a_3631_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
lean_del_object(v___x_3633_);
v___x_3636_ = lean_box(0);
v___x_3637_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3638_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3625_, v_expr_3626_, v___x_3636_, v___x_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v_expr_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3653_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3638_, 1);
v_expr_3640_ = lean_ctor_get(v_a_3615_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_a_3615_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; 
v_unused_3654_ = lean_ctor_get(v_a_3615_, 1);
lean_dec(v_unused_3654_);
v___x_3642_ = v_a_3615_;
v_isShared_3643_ = v_isSharedCheck_3653_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_expr_3640_);
lean_dec(v_a_3615_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3653_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3644_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3645_ = l_Lean_indentExpr(v_expr_3640_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 7);
lean_ctor_set(v___x_3642_, 1, v___x_3645_);
lean_ctor_set(v___x_3642_, 0, v___x_3644_);
v___x_3647_ = v___x_3642_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 7);
lean_ctor_set(v___x_3628_, 1, v_a_3639_);
lean_ctor_set(v___x_3628_, 0, v___x_3647_);
v___x_3649_ = v___x_3628_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_a_3639_);
v___x_3649_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3649_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
return v___x_3650_;
}
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_del_object(v___x_3628_);
lean_dec_ref(v_a_3615_);
v_a_3655_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3638_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3638_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
lean_del_object(v___x_3628_);
lean_dec_ref(v_expr_3626_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3615_);
v___x_3663_ = lean_box(0);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3663_);
v___x_3665_ = v___x_3633_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_del_object(v___x_3628_);
lean_dec_ref(v_expr_3626_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3615_);
v_a_3668_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3630_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3630_);
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
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec_ref(v_a_3616_);
lean_dec_ref(v_a_3615_);
v_a_3678_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3624_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3624_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3686_, v_a_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec(v___y_3688_);
return v_res_3695_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
if (lean_obj_tag(v_e_3699_) == 5)
{
lean_object* v_fn_3707_; lean_object* v_arg_3708_; lean_object* v___x_3709_; 
v_fn_3707_ = lean_ctor_get(v_e_3699_, 0);
v_arg_3708_ = lean_ctor_get(v_e_3699_, 1);
lean_inc_ref(v_fn_3707_);
v___x_3709_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3707_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3711_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
lean_inc_ref(v_arg_3708_);
v___x_3711_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3708_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3734_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3714_ = v___x_3711_;
v_isShared_3715_ = v_isSharedCheck_3734_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3711_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3734_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v_expr_3716_; size_t v___x_3717_; size_t v___x_3718_; uint8_t v___x_3719_; 
v_expr_3716_ = lean_ctor_get(v_a_3712_, 0);
lean_inc_ref(v_expr_3716_);
lean_dec(v_a_3712_);
v___x_3717_ = lean_ptr_addr(v_fn_3707_);
v___x_3718_ = lean_ptr_addr(v_a_3710_);
v___x_3719_ = lean_usize_dec_eq(v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; lean_object* v___x_3722_; 
lean_dec_ref_known(v_e_3699_, 2);
v___x_3720_ = l_Lean_Expr_app___override(v_a_3710_, v_expr_3716_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3720_);
v___x_3722_ = v___x_3714_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
else
{
size_t v___x_3724_; size_t v___x_3725_; uint8_t v___x_3726_; 
v___x_3724_ = lean_ptr_addr(v_arg_3708_);
v___x_3725_ = lean_ptr_addr(v_expr_3716_);
v___x_3726_ = lean_usize_dec_eq(v___x_3724_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_dec_ref_known(v_e_3699_, 2);
v___x_3727_ = l_Lean_Expr_app___override(v_a_3710_, v_expr_3716_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3727_);
v___x_3729_ = v___x_3714_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
else
{
lean_object* v___x_3732_; 
lean_dec_ref(v_expr_3716_);
lean_dec(v_a_3710_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v_e_3699_);
v___x_3732_ = v___x_3714_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_e_3699_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec(v_a_3710_);
lean_dec_ref_known(v_e_3699_, 2);
v_a_3735_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3711_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3711_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
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
else
{
lean_dec_ref_known(v_e_3699_, 2);
return v___x_3709_;
}
}
else
{
lean_object* v___x_3743_; 
v___x_3743_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3752_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3752_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3752_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v_expr_3748_; lean_object* v___x_3750_; 
v_expr_3748_ = lean_ctor_get(v_a_3744_, 0);
lean_inc_ref(v_expr_3748_);
lean_dec(v_a_3744_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v_expr_3748_);
v___x_3750_ = v___x_3746_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_expr_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_a_3753_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3743_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3743_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec(v_a_3762_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
if (lean_obj_tag(v_e_3770_) == 5)
{
lean_object* v_fn_3778_; lean_object* v_arg_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_fn_3778_ = lean_ctor_get(v_e_3770_, 0);
v_arg_3779_ = lean_ctor_get(v_e_3770_, 1);
lean_inc_ref_n(v_fn_3778_, 2);
v___x_3780_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3780_, 0, v_fn_3778_);
v___x_3781_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3778_, v___x_3780_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
lean_inc_ref(v_arg_3779_);
v___x_3783_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3779_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3785_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3770_, v_a_3782_, v_a_3784_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_3785_;
}
else
{
lean_dec(v_a_3782_);
lean_dec_ref_known(v_e_3770_, 2);
return v___x_3783_;
}
}
else
{
lean_dec_ref_known(v_e_3770_, 2);
return v___x_3781_;
}
}
else
{
lean_object* v___x_3786_; 
v___x_3786_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_3786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
uint8_t v___x_3795_; 
v___x_3795_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3788_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; 
v___x_3796_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3806_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3806_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3806_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3804_; 
v___x_3801_ = lean_box(0);
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v_a_3797_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v___x_3802_);
v___x_3804_ = v___x_3799_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
v_a_3807_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3796_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3796_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Lean_Expr_getAppFn(v_e_3787_);
if (lean_obj_tag(v___x_3815_) == 2)
{
lean_object* v_mvarId_3816_; lean_object* v_dummy_3817_; lean_object* v_nargs_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_mvarId_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_mvarId_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v_dummy_3817_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3818_ = l_Lean_Expr_getAppNumArgs(v_e_3787_);
lean_inc(v_nargs_3818_);
v___x_3819_ = lean_mk_array(v_nargs_3818_, v_dummy_3817_);
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = lean_nat_sub(v_nargs_3818_, v___x_3820_);
lean_dec(v_nargs_3818_);
lean_inc_ref(v_e_3787_);
v___x_3822_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3787_, v___x_3819_, v___x_3821_);
v___x_3823_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3816_, v___x_3822_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
lean_dec(v_mvarId_3816_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3824_; 
lean_dec_ref_known(v___x_3823_, 1);
v___x_3824_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
return v___x_3824_;
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v_e_3787_);
v_a_3825_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3823_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3823_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v___x_3833_; 
lean_dec_ref(v___x_3815_);
v___x_3833_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
return v___x_3833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec(v_a_3835_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3852_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
return v___x_3853_;
}
else
{
return v___x_3851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec(v_a_3855_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3863_, lean_object* v_fvars_3864_, lean_object* v_doms_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3863_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___x_3875_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3864_, v_doms_3865_, v_a_3874_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3875_;
}
else
{
return v___x_3873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3876_, lean_object* v_fvars_3877_, lean_object* v_doms_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3876_, v_fvars_3877_, v_doms_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v_doms_3878_);
lean_dec_ref(v_fvars_3877_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3887_, lean_object* v_fvars_3888_, lean_object* v_doms_3889_, lean_object* v_e_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3890_, v_a_3892_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3898_, 1);
if (lean_obj_tag(v_a_3899_) == 1)
{
lean_object* v_val_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec_ref(v_e_3890_);
v_val_3900_ = lean_ctor_get(v_a_3899_, 0);
lean_inc(v_val_3900_);
lean_dec_ref_known(v_a_3899_, 1);
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3902_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3902_, 0, v_fvars_3888_);
lean_closure_set(v___x_3902_, 1, v_doms_3889_);
lean_closure_set(v___x_3902_, 2, v_val_3900_);
v___x_3903_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3887_, v___x_3901_, v___x_3902_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
return v___x_3903_;
}
else
{
lean_dec(v_a_3899_);
if (lean_obj_tag(v_e_3890_) == 7)
{
lean_object* v_binderName_3904_; lean_object* v_binderType_3905_; lean_object* v_body_3906_; uint8_t v_binderInfo_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_binderName_3904_ = lean_ctor_get(v_e_3890_, 0);
lean_inc(v_binderName_3904_);
v_binderType_3905_ = lean_ctor_get(v_e_3890_, 1);
lean_inc_ref(v_binderType_3905_);
v_body_3906_ = lean_ctor_get(v_e_3890_, 2);
lean_inc_ref(v_body_3906_);
v_binderInfo_3907_ = lean_ctor_get_uint8(v_e_3890_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3890_, 3);
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3909_ = lean_expr_instantiate_rev(v_binderType_3905_, v_fvars_3888_);
lean_dec_ref(v_binderType_3905_);
v___x_3910_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3910_, 0, v___x_3909_);
lean_inc_ref(v_lctx_3887_);
v___x_3911_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3887_, v___x_3908_, v___x_3910_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v_expr_3915_; uint8_t v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc_n(v_a_3914_, 2);
lean_dec_ref_known(v___x_3913_, 1);
v_expr_3915_ = lean_ctor_get(v_a_3912_, 0);
v___x_3916_ = 0;
lean_inc_ref(v_expr_3915_);
v___x_3917_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3887_, v_a_3914_, v_binderName_3904_, v_expr_3915_, v_binderInfo_3907_, v___x_3916_);
v___x_3918_ = l_Lean_Expr_fvar___override(v_a_3914_);
v___x_3919_ = lean_array_push(v_fvars_3888_, v___x_3918_);
v___x_3920_ = lean_array_push(v_doms_3889_, v_a_3912_);
v_lctx_3887_ = v___x_3917_;
v_fvars_3888_ = v___x_3919_;
v_doms_3889_ = v___x_3920_;
v_e_3890_ = v_body_3906_;
goto _start;
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec(v_a_3912_);
lean_dec_ref(v_body_3906_);
lean_dec(v_binderName_3904_);
lean_dec_ref(v_doms_3889_);
lean_dec_ref(v_fvars_3888_);
lean_dec_ref(v_lctx_3887_);
v_a_3922_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3913_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3913_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_dec_ref(v_body_3906_);
lean_dec(v_binderName_3904_);
lean_dec_ref(v_doms_3889_);
lean_dec_ref(v_fvars_3888_);
lean_dec_ref(v_lctx_3887_);
return v___x_3911_;
}
}
else
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___f_3932_; lean_object* v___x_3933_; 
v___x_3930_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3931_ = lean_expr_instantiate_rev(v_e_3890_, v_fvars_3888_);
lean_dec_ref(v_e_3890_);
v___f_3932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3932_, 0, v___x_3931_);
lean_closure_set(v___f_3932_, 1, v_fvars_3888_);
lean_closure_set(v___f_3932_, 2, v_doms_3889_);
v___x_3933_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3887_, v___x_3930_, v___f_3932_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
return v___x_3933_;
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref(v_e_3890_);
lean_dec_ref(v_doms_3889_);
lean_dec_ref(v_fvars_3888_);
lean_dec_ref(v_lctx_3887_);
v_a_3934_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3898_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3898_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
uint32_t v___x_3950_; uint8_t v___x_3951_; 
v___x_3950_ = 5;
v___x_3951_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3942_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v_lctx_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_lctx_3952_ = lean_ctor_get(v_a_3945_, 2);
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3952_);
v___x_3954_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3952_, v___x_3953_, v___x_3953_, v_e_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3954_;
}
else
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3955_ = lean_box(0);
v___x_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3956_, 0, v_e_3942_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
return v___x_3957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec(v_a_3959_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_3967_, lean_object* v_e_3968_, lean_object* v_typeName_3969_, lean_object* v_idx_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_3967_, v_e_3968_, v_typeName_3969_, v_idx_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec(v___y_3971_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec(v_a_3980_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_3999_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___x_3997_, 1);
v___x_3999_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_3988_, v_a_3998_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
return v___x_3999_;
}
else
{
lean_dec_ref(v_fvars_3988_);
return v___x_3997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec(v___y_4002_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4010_, lean_object* v_fvars_4011_, lean_object* v_e_4012_, lean_object* v_letFVars_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
switch(lean_obj_tag(v_e_4012_))
{
case 6:
{
lean_object* v_binderName_4021_; lean_object* v_binderType_4022_; lean_object* v_body_4023_; uint8_t v_binderInfo_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_binderName_4021_ = lean_ctor_get(v_e_4012_, 0);
lean_inc(v_binderName_4021_);
v_binderType_4022_ = lean_ctor_get(v_e_4012_, 1);
lean_inc_ref(v_binderType_4022_);
v_body_4023_ = lean_ctor_get(v_e_4012_, 2);
lean_inc_ref(v_body_4023_);
v_binderInfo_4024_ = lean_ctor_get_uint8(v_e_4012_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4012_, 3);
v___x_4025_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4010_);
lean_inc(v_letFVars_4013_);
v___x_4026_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4011_, v_letFVars_4013_, v_lctx_4010_, v___x_4025_, v_binderType_4022_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec_ref(v_binderType_4022_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v___x_4028_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v_expr_4030_; uint8_t v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc_n(v_a_4029_, 2);
lean_dec_ref_known(v___x_4028_, 1);
v_expr_4030_ = lean_ctor_get(v_a_4027_, 0);
lean_inc_ref(v_expr_4030_);
lean_dec(v_a_4027_);
v___x_4031_ = 0;
v___x_4032_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4010_, v_a_4029_, v_binderName_4021_, v_expr_4030_, v_binderInfo_4024_, v___x_4031_);
v___x_4033_ = l_Lean_Expr_fvar___override(v_a_4029_);
v___x_4034_ = lean_array_push(v_fvars_4011_, v___x_4033_);
v_lctx_4010_ = v___x_4032_;
v_fvars_4011_ = v___x_4034_;
v_e_4012_ = v_body_4023_;
goto _start;
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec(v_a_4027_);
lean_dec_ref(v_body_4023_);
lean_dec(v_binderName_4021_);
lean_dec(v_letFVars_4013_);
lean_dec_ref(v_fvars_4011_);
lean_dec_ref(v_lctx_4010_);
v_a_4036_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4028_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4028_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_dec_ref(v_body_4023_);
lean_dec(v_binderName_4021_);
lean_dec(v_letFVars_4013_);
lean_dec_ref(v_fvars_4011_);
lean_dec_ref(v_lctx_4010_);
return v___x_4026_;
}
}
case 8:
{
lean_object* v_declName_4044_; lean_object* v_type_4045_; lean_object* v_value_4046_; lean_object* v_body_4047_; uint8_t v_nondep_4048_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v_declName_4044_ = lean_ctor_get(v_e_4012_, 0);
lean_inc(v_declName_4044_);
v_type_4045_ = lean_ctor_get(v_e_4012_, 1);
lean_inc_ref(v_type_4045_);
v_value_4046_ = lean_ctor_get(v_e_4012_, 2);
lean_inc_ref(v_value_4046_);
v_body_4047_ = lean_ctor_get(v_e_4012_, 3);
lean_inc_ref(v_body_4047_);
v_nondep_4048_ = lean_ctor_get_uint8(v_e_4012_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4012_, 4);
v___x_4062_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4010_);
lean_inc(v_letFVars_4013_);
v___x_4063_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4011_, v_letFVars_4013_, v_lctx_4010_, v___x_4062_, v_type_4045_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec_ref(v_type_4045_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4010_);
lean_inc(v_letFVars_4013_);
v___x_4066_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4011_, v_letFVars_4013_, v_lctx_4010_, v___x_4065_, v_value_4046_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec_ref(v_value_4046_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; uint8_t v___x_4097_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4097_ = l_List_isEmpty___redArg(v_letFVars_4013_);
if (v___x_4097_ == 0)
{
lean_object* v___f_4098_; lean_object* v___x_4099_; 
lean_inc(v_a_4064_);
lean_inc(v_a_4067_);
v___f_4098_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4098_, 0, v_a_4067_);
lean_closure_set(v___f_4098_, 1, v_a_4064_);
lean_inc_ref(v_lctx_4010_);
v___x_4099_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4010_, v___f_4098_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_dec_ref_known(v___x_4099_, 1);
v___y_4069_ = v_a_4014_;
v___y_4070_ = v_a_4015_;
v___y_4071_ = v_a_4016_;
v___y_4072_ = v_a_4017_;
v___y_4073_ = v_a_4018_;
v___y_4074_ = v_a_4019_;
goto v___jp_4068_;
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_a_4067_);
lean_dec(v_a_4064_);
lean_dec_ref(v_body_4047_);
lean_dec(v_declName_4044_);
lean_dec(v_letFVars_4013_);
lean_dec_ref(v_fvars_4011_);
lean_dec_ref(v_lctx_4010_);
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4099_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4099_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
v___y_4069_ = v_a_4014_;
v___y_4070_ = v_a_4015_;
v___y_4071_ = v_a_4016_;
v___y_4072_ = v_a_4017_;
v___y_4073_ = v_a_4018_;
v___y_4074_ = v_a_4019_;
goto v___jp_4068_;
}
v___jp_4068_:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v_expr_4077_; lean_object* v_expr_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4087_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
v_expr_4077_ = lean_ctor_get(v_a_4064_, 0);
lean_inc_ref(v_expr_4077_);
lean_dec(v_a_4064_);
v_expr_4078_ = lean_ctor_get(v_a_4067_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_a_4067_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v_a_4067_, 1);
lean_dec(v_unused_4088_);
v___x_4080_ = v_a_4067_;
v_isShared_4081_ = v_isSharedCheck_4087_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_expr_4078_);
lean_dec(v_a_4067_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4087_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
uint8_t v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = 0;
lean_inc(v_a_4076_);
v___x_4083_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4010_, v_a_4076_, v_declName_4044_, v_expr_4077_, v_expr_4078_, v_nondep_4048_, v___x_4082_);
if (v_nondep_4048_ == 0)
{
lean_object* v___x_4085_; 
lean_inc(v_a_4076_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set_tag(v___x_4080_, 1);
lean_ctor_set(v___x_4080_, 1, v_letFVars_4013_);
lean_ctor_set(v___x_4080_, 0, v_a_4076_);
v___x_4085_ = v___x_4080_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4076_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_letFVars_4013_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
v___y_4050_ = v___y_4072_;
v___y_4051_ = v___x_4083_;
v___y_4052_ = v___y_4073_;
v___y_4053_ = v___y_4069_;
v___y_4054_ = v___y_4074_;
v___y_4055_ = v___y_4070_;
v___y_4056_ = v___y_4071_;
v___y_4057_ = v_a_4076_;
v___y_4058_ = v___x_4085_;
goto v___jp_4049_;
}
}
else
{
lean_del_object(v___x_4080_);
v___y_4050_ = v___y_4072_;
v___y_4051_ = v___x_4083_;
v___y_4052_ = v___y_4073_;
v___y_4053_ = v___y_4069_;
v___y_4054_ = v___y_4074_;
v___y_4055_ = v___y_4070_;
v___y_4056_ = v___y_4071_;
v___y_4057_ = v_a_4076_;
v___y_4058_ = v_letFVars_4013_;
goto v___jp_4049_;
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v_a_4067_);
lean_dec(v_a_4064_);
lean_dec_ref(v_body_4047_);
lean_dec(v_declName_4044_);
lean_dec(v_letFVars_4013_);
lean_dec_ref(v_fvars_4011_);
lean_dec_ref(v_lctx_4010_);
v_a_4089_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4075_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4075_);
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
}
else
{
lean_dec(v_a_4064_);
lean_dec_ref(v_body_4047_);
lean_dec(v_declName_4044_);
lean_dec(v_letFVars_4013_);
lean_dec_ref(v_fvars_4011_);
lean_dec_ref(v_lctx_4010_);
return v___x_4066_;
}
}
else
{
lean_dec_ref(v_body_4047_);
lean_dec_ref(v_value_4046_);
lean_dec(v_declName_4044_);
lean_dec(v_letFVars_4013_);
lean_dec_ref(v_fvars_4011_);
lean_dec_ref(v_lctx_4010_);
return v___x_4063_;
}
v___jp_4049_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = l_Lean_Expr_fvar___override(v___y_4057_);
v___x_4060_ = lean_array_push(v_fvars_4011_, v___x_4059_);
v_lctx_4010_ = v___y_4051_;
v_fvars_4011_ = v___x_4060_;
v_e_4012_ = v_body_4047_;
v_letFVars_4013_ = v___y_4058_;
v_a_4014_ = v___y_4053_;
v_a_4015_ = v___y_4055_;
v_a_4016_ = v___y_4056_;
v_a_4017_ = v___y_4050_;
v_a_4018_ = v___y_4052_;
v_a_4019_ = v___y_4054_;
goto _start;
}
}
default: 
{
lean_object* v___f_4108_; lean_object* v___x_4109_; 
lean_inc_ref(v_fvars_4011_);
v___f_4108_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4108_, 0, v_fvars_4011_);
v___x_4109_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4011_, v_letFVars_4013_, v_lctx_4010_, v___f_4108_, v_e_4012_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec_ref(v_e_4012_);
lean_dec_ref(v_fvars_4011_);
return v___x_4109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_){
_start:
{
uint32_t v___x_4118_; uint8_t v___x_4119_; 
v___x_4118_ = 5;
v___x_4119_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4110_, v___x_4118_);
if (v___x_4119_ == 0)
{
lean_object* v_lctx_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v_lctx_4120_ = lean_ctor_get(v_a_4113_, 2);
v___x_4121_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4111_);
lean_inc_ref(v_lctx_4120_);
v___x_4122_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4120_, v___x_4121_, v_e_4110_, v_a_4111_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_);
return v___x_4122_;
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4123_ = lean_box(0);
v___x_4124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4124_, 0, v_e_4110_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
return v___x_4125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec(v_a_4127_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
switch(lean_obj_tag(v_e_4135_))
{
case 0:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4143_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4144_ = l_Lean_MessageData_ofExpr(v_e_4135_);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4143_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4145_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4146_;
}
case 1:
{
lean_object* v___x_4147_; 
v___x_4147_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4135_, v___y_4138_, v___y_4140_, v___y_4141_);
return v___x_4147_;
}
case 2:
{
lean_object* v___x_4148_; 
v___x_4148_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4148_;
}
case 3:
{
lean_object* v_u_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_u_4149_ = lean_ctor_get(v_e_4135_, 0);
lean_inc(v_u_4149_);
v___x_4150_ = l_Lean_Level_succ___override(v_u_4149_);
v___x_4151_ = l_Lean_Expr_sort___override(v___x_4150_);
v___x_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
v___x_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4153_, 0, v_e_4135_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
return v___x_4154_;
}
case 4:
{
lean_object* v___x_4155_; 
v___x_4155_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4155_;
}
case 5:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_inc_ref(v_e_4135_);
v___x_4156_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4156_, 0, v_e_4135_);
v___x_4157_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4135_, v___x_4156_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4157_;
}
case 7:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
lean_inc_ref(v_e_4135_);
v___x_4158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4158_, 0, v_e_4135_);
v___x_4159_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4135_, v___x_4158_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4159_;
}
case 9:
{
lean_object* v_a_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_a_4160_ = lean_ctor_get(v_e_4135_, 0);
v___x_4161_ = l_Lean_Literal_type(v_a_4160_);
v___x_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
v___x_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4163_, 0, v_e_4135_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
case 10:
{
lean_object* v_data_4165_; lean_object* v_expr_4166_; lean_object* v___x_4167_; 
v_data_4165_ = lean_ctor_get(v_e_4135_, 0);
v_expr_4166_ = lean_ctor_get(v_e_4135_, 1);
lean_inc_ref(v_expr_4166_);
v___x_4167_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4166_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4190_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4170_ = v___x_4167_;
v_isShared_4171_ = v_isSharedCheck_4190_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4190_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v_expr_4172_; lean_object* v_type_x3f_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4189_; 
v_expr_4172_ = lean_ctor_get(v_a_4168_, 0);
v_type_x3f_4173_ = lean_ctor_get(v_a_4168_, 1);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_a_4168_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4175_ = v_a_4168_;
v_isShared_4176_ = v_isSharedCheck_4189_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_type_x3f_4173_);
lean_inc(v_expr_4172_);
lean_dec(v_a_4168_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4189_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___y_4178_; size_t v___x_4185_; size_t v___x_4186_; uint8_t v___x_4187_; 
v___x_4185_ = lean_ptr_addr(v_expr_4166_);
v___x_4186_ = lean_ptr_addr(v_expr_4172_);
v___x_4187_ = lean_usize_dec_eq(v___x_4185_, v___x_4186_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; 
lean_inc(v_data_4165_);
lean_dec_ref_known(v_e_4135_, 2);
v___x_4188_ = l_Lean_Expr_mdata___override(v_data_4165_, v_expr_4172_);
v___y_4178_ = v___x_4188_;
goto v___jp_4177_;
}
else
{
lean_dec_ref(v_expr_4172_);
v___y_4178_ = v_e_4135_;
goto v___jp_4177_;
}
v___jp_4177_:
{
lean_object* v___x_4180_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___y_4178_);
v___x_4180_ = v___x_4175_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___y_4178_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v_type_x3f_4173_);
v___x_4180_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4182_; 
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 0, v___x_4180_);
v___x_4182_ = v___x_4170_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4135_, 2);
return v___x_4167_;
}
}
case 11:
{
lean_object* v_typeName_4191_; lean_object* v_idx_4192_; lean_object* v_struct_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; 
v_typeName_4191_ = lean_ctor_get(v_e_4135_, 0);
v_idx_4192_ = lean_ctor_get(v_e_4135_, 1);
v_struct_4193_ = lean_ctor_get(v_e_4135_, 2);
lean_inc(v_idx_4192_);
lean_inc(v_typeName_4191_);
lean_inc_ref(v_e_4135_);
lean_inc_ref(v_struct_4193_);
v___f_4194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4194_, 0, v_struct_4193_);
lean_closure_set(v___f_4194_, 1, v_e_4135_);
lean_closure_set(v___f_4194_, 2, v_typeName_4191_);
lean_closure_set(v___f_4194_, 3, v_idx_4192_);
v___x_4195_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4135_, v___f_4194_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4195_;
}
default: 
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_inc_ref(v_e_4135_);
v___x_4196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4196_, 0, v_e_4135_);
v___x_4197_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4135_, v___x_4196_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4197_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4198_; double v___x_4199_; 
v___x_4198_ = lean_unsigned_to_nat(1000000000u);
v___x_4199_ = lean_float_of_nat(v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_toCold_4208_; lean_object* v_options_4209_; uint8_t v_hasTrace_4210_; 
v_toCold_4208_ = lean_ctor_get(v_a_4205_, 0);
v_options_4209_ = lean_ctor_get(v_toCold_4208_, 2);
v_hasTrace_4210_ = lean_ctor_get_uint8(v_options_4209_, sizeof(void*)*1);
if (v_hasTrace_4210_ == 0)
{
lean_object* v___x_4211_; 
v___x_4211_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
return v___x_4211_;
}
else
{
lean_object* v_inheritedTraceOptions_4212_; lean_object* v___f_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v_a_4221_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v_a_4236_; 
v_inheritedTraceOptions_4212_ = lean_ctor_get(v_toCold_4208_, 11);
lean_inc_ref(v_e_4200_);
v___f_4213_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4213_, 0, v_e_4200_);
v___x_4214_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4215_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4216_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4217_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4212_, v_options_4209_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = l_Lean_trace_profiler;
v___x_4295_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4209_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; 
lean_dec_ref(v___f_4213_);
v___x_4296_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
return v___x_4296_;
}
else
{
goto v___jp_4245_;
}
}
else
{
goto v___jp_4245_;
}
v___jp_4218_:
{
lean_object* v___x_4222_; double v___x_4223_; double v___x_4224_; double v___x_4225_; double v___x_4226_; double v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4222_ = lean_io_mono_nanos_now();
v___x_4223_ = lean_float_of_nat(v___y_4219_);
v___x_4224_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4225_ = lean_float_div(v___x_4223_, v___x_4224_);
v___x_4226_ = lean_float_of_nat(v___x_4222_);
v___x_4227_ = lean_float_div(v___x_4226_, v___x_4224_);
v___x_4228_ = lean_box_float(v___x_4225_);
v___x_4229_ = lean_box_float(v___x_4227_);
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4228_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v_a_4221_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4214_, v_hasTrace_4210_, v___x_4215_, v_options_4209_, v___x_4217_, v___y_4220_, v___f_4213_, v___x_4231_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
return v___x_4232_;
}
v___jp_4233_:
{
lean_object* v___x_4237_; double v___x_4238_; double v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4237_ = lean_io_get_num_heartbeats();
v___x_4238_ = lean_float_of_nat(v___y_4235_);
v___x_4239_ = lean_float_of_nat(v___x_4237_);
v___x_4240_ = lean_box_float(v___x_4238_);
v___x_4241_ = lean_box_float(v___x_4239_);
v___x_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4240_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4243_, 0, v_a_4236_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4214_, v_hasTrace_4210_, v___x_4215_, v_options_4209_, v___x_4217_, v___y_4234_, v___f_4213_, v___x_4243_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
return v___x_4244_;
}
v___jp_4245_:
{
lean_object* v___x_4246_; 
v___x_4246_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4206_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___x_4248_; uint8_t v___x_4249_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4247_);
lean_dec_ref_known(v___x_4246_, 1);
v___x_4248_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4249_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4209_, v___x_4248_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = lean_io_mono_nanos_now();
v___x_4251_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4251_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4251_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
lean_ctor_set_tag(v___x_4254_, 1);
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
v___y_4219_ = v___x_4250_;
v___y_4220_ = v_a_4247_;
v_a_4221_ = v___x_4257_;
goto v___jp_4218_;
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
v_a_4260_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4251_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4251_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
lean_ctor_set_tag(v___x_4262_, 0);
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
v___y_4219_ = v___x_4250_;
v___y_4220_ = v_a_4247_;
v_a_4221_ = v___x_4265_;
goto v___jp_4218_;
}
}
}
}
else
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_io_get_num_heartbeats();
v___x_4269_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set_tag(v___x_4272_, 1);
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
v___y_4234_ = v_a_4247_;
v___y_4235_ = v___x_4268_;
v_a_4236_ = v___x_4275_;
goto v___jp_4233_;
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v_a_4278_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4269_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4269_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set_tag(v___x_4280_, 0);
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
v___y_4234_ = v_a_4247_;
v___y_4235_ = v___x_4268_;
v_a_4236_ = v___x_4283_;
goto v___jp_4233_;
}
}
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_dec_ref(v___f_4213_);
lean_dec_ref(v_e_4200_);
v_a_4286_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4246_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4246_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
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
return v___x_4291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4297_, lean_object* v_e_4298_, lean_object* v_typeName_4299_, lean_object* v_idx_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4297_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4310_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4308_, 1);
v___x_4310_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4298_, v_typeName_4299_, v_idx_4300_, v_a_4309_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
return v___x_4310_;
}
else
{
lean_dec(v_idx_4300_);
lean_dec(v_typeName_4299_);
lean_dec_ref(v_e_4298_);
return v___x_4308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec(v_a_4312_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4320_, lean_object* v_fvars_4321_, lean_object* v_doms_4322_, lean_object* v_e_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4320_, v_fvars_4321_, v_doms_4322_, v_e_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec(v_a_4324_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec(v___y_4333_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4341_, lean_object* v_fvars_4342_, lean_object* v_e_4343_, lean_object* v_letFVars_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4341_, v_fvars_4342_, v_e_4343_, v_letFVars_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec(v_a_4345_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4353_, lean_object* v_lctx_4354_, lean_object* v_localInsts_4355_, lean_object* v_x_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4354_, v_localInsts_4355_, v_x_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4365_, lean_object* v_lctx_4366_, lean_object* v_localInsts_4367_, lean_object* v_x_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4365_, v_lctx_4366_, v_localInsts_4367_, v_x_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec(v___y_4369_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4377_, lean_object* v_lctx_4378_, lean_object* v_x_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4378_, v_x_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4388_, lean_object* v_lctx_4389_, lean_object* v_x_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4388_, v_lctx_4389_, v_x_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec(v___y_4391_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4404_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec(v___y_4407_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4420_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec(v___y_4423_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4431_, lean_object* v_x_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4432_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4441_, lean_object* v_x_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4441_, v_x_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec(v___y_4443_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4451_, lean_object* v_data_4452_, lean_object* v_ref_4453_, lean_object* v_msg_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4451_, v_data_4452_, v_ref_4453_, v_msg_4454_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4463_, lean_object* v_data_4464_, lean_object* v_ref_4465_, lean_object* v_msg_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4463_, v_data_4464_, v_ref_4465_, v_msg_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec(v___y_4467_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4475_){
_start:
{
lean_object* v___x_4477_; lean_object* v_traceState_4478_; lean_object* v_traces_4479_; lean_object* v___x_4480_; lean_object* v_traceState_4481_; lean_object* v_env_4482_; lean_object* v_nextMacroScope_4483_; lean_object* v_ngen_4484_; lean_object* v_auxDeclNGen_4485_; lean_object* v_cache_4486_; lean_object* v_messages_4487_; lean_object* v_infoState_4488_; lean_object* v_snapshotTasks_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4510_; 
v___x_4477_ = lean_st_ref_get(v___y_4475_);
v_traceState_4478_ = lean_ctor_get(v___x_4477_, 4);
lean_inc_ref(v_traceState_4478_);
lean_dec(v___x_4477_);
v_traces_4479_ = lean_ctor_get(v_traceState_4478_, 0);
lean_inc_ref(v_traces_4479_);
lean_dec_ref(v_traceState_4478_);
v___x_4480_ = lean_st_ref_take(v___y_4475_);
v_traceState_4481_ = lean_ctor_get(v___x_4480_, 4);
v_env_4482_ = lean_ctor_get(v___x_4480_, 0);
v_nextMacroScope_4483_ = lean_ctor_get(v___x_4480_, 1);
v_ngen_4484_ = lean_ctor_get(v___x_4480_, 2);
v_auxDeclNGen_4485_ = lean_ctor_get(v___x_4480_, 3);
v_cache_4486_ = lean_ctor_get(v___x_4480_, 5);
v_messages_4487_ = lean_ctor_get(v___x_4480_, 6);
v_infoState_4488_ = lean_ctor_get(v___x_4480_, 7);
v_snapshotTasks_4489_ = lean_ctor_get(v___x_4480_, 8);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4491_ = v___x_4480_;
v_isShared_4492_ = v_isSharedCheck_4510_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_snapshotTasks_4489_);
lean_inc(v_infoState_4488_);
lean_inc(v_messages_4487_);
lean_inc(v_cache_4486_);
lean_inc(v_traceState_4481_);
lean_inc(v_auxDeclNGen_4485_);
lean_inc(v_ngen_4484_);
lean_inc(v_nextMacroScope_4483_);
lean_inc(v_env_4482_);
lean_dec(v___x_4480_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4510_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
uint64_t v_tid_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4508_; 
v_tid_4493_ = lean_ctor_get_uint64(v_traceState_4481_, sizeof(void*)*1);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_traceState_4481_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v_traceState_4481_, 0);
lean_dec(v_unused_4509_);
v___x_4495_ = v_traceState_4481_;
v_isShared_4496_ = v_isSharedCheck_4508_;
goto v_resetjp_4494_;
}
else
{
lean_dec(v_traceState_4481_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4508_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4497_ = lean_unsigned_to_nat(32u);
v___x_4498_ = lean_mk_empty_array_with_capacity(v___x_4497_);
lean_dec_ref(v___x_4498_);
v___x_4499_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4499_);
v___x_4501_ = v___x_4495_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4499_);
lean_ctor_set_uint64(v_reuseFailAlloc_4507_, sizeof(void*)*1, v_tid_4493_);
v___x_4501_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4503_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 4, v___x_4501_);
v___x_4503_ = v___x_4491_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_env_4482_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_nextMacroScope_4483_);
lean_ctor_set(v_reuseFailAlloc_4506_, 2, v_ngen_4484_);
lean_ctor_set(v_reuseFailAlloc_4506_, 3, v_auxDeclNGen_4485_);
lean_ctor_set(v_reuseFailAlloc_4506_, 4, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4506_, 5, v_cache_4486_);
lean_ctor_set(v_reuseFailAlloc_4506_, 6, v_messages_4487_);
lean_ctor_set(v_reuseFailAlloc_4506_, 7, v_infoState_4488_);
lean_ctor_set(v_reuseFailAlloc_4506_, 8, v_snapshotTasks_4489_);
v___x_4503_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_st_ref_put(v___y_4475_, v___x_4503_);
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v_traces_4479_);
return v___x_4505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4511_);
lean_dec(v___y_4511_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v___x_4519_; 
v___x_4519_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4526_, lean_object* v_zetaDeltaFVarIds_4527_, lean_object* v_a_x3f_4528_){
_start:
{
lean_object* v___x_4530_; lean_object* v_mctx_4531_; lean_object* v_cache_4532_; lean_object* v_postponed_4533_; lean_object* v_diag_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4544_; 
v___x_4530_ = lean_st_ref_take(v___y_4526_);
v_mctx_4531_ = lean_ctor_get(v___x_4530_, 0);
v_cache_4532_ = lean_ctor_get(v___x_4530_, 1);
v_postponed_4533_ = lean_ctor_get(v___x_4530_, 3);
v_diag_4534_ = lean_ctor_get(v___x_4530_, 4);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4544_ == 0)
{
lean_object* v_unused_4545_; 
v_unused_4545_ = lean_ctor_get(v___x_4530_, 2);
lean_dec(v_unused_4545_);
v___x_4536_ = v___x_4530_;
v_isShared_4537_ = v_isSharedCheck_4544_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_diag_4534_);
lean_inc(v_postponed_4533_);
lean_inc(v_cache_4532_);
lean_inc(v_mctx_4531_);
lean_dec(v___x_4530_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4544_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 2, v_zetaDeltaFVarIds_4527_);
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_mctx_4531_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_cache_4532_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_zetaDeltaFVarIds_4527_);
lean_ctor_set(v_reuseFailAlloc_4543_, 3, v_postponed_4533_);
lean_ctor_set(v_reuseFailAlloc_4543_, 4, v_diag_4534_);
v___x_4539_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_st_ref_put(v___y_4526_, v___x_4539_);
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4546_, lean_object* v_zetaDeltaFVarIds_4547_, lean_object* v_a_x3f_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4546_, v_zetaDeltaFVarIds_4547_, v_a_x3f_4548_);
lean_dec(v_a_x3f_4548_);
lean_dec(v___y_4546_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4551_, lean_object* v_msg_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v_ref_4558_; lean_object* v___x_4559_; lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4604_; 
v_ref_4558_ = lean_ctor_get(v___y_4555_, 2);
v___x_4559_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4562_ = v___x_4559_;
v_isShared_4563_ = v_isSharedCheck_4604_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4559_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4604_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4564_; lean_object* v_traceState_4565_; lean_object* v_env_4566_; lean_object* v_nextMacroScope_4567_; lean_object* v_ngen_4568_; lean_object* v_auxDeclNGen_4569_; lean_object* v_cache_4570_; lean_object* v_messages_4571_; lean_object* v_infoState_4572_; lean_object* v_snapshotTasks_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4603_; 
v___x_4564_ = lean_st_ref_take(v___y_4556_);
v_traceState_4565_ = lean_ctor_get(v___x_4564_, 4);
v_env_4566_ = lean_ctor_get(v___x_4564_, 0);
v_nextMacroScope_4567_ = lean_ctor_get(v___x_4564_, 1);
v_ngen_4568_ = lean_ctor_get(v___x_4564_, 2);
v_auxDeclNGen_4569_ = lean_ctor_get(v___x_4564_, 3);
v_cache_4570_ = lean_ctor_get(v___x_4564_, 5);
v_messages_4571_ = lean_ctor_get(v___x_4564_, 6);
v_infoState_4572_ = lean_ctor_get(v___x_4564_, 7);
v_snapshotTasks_4573_ = lean_ctor_get(v___x_4564_, 8);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4575_ = v___x_4564_;
v_isShared_4576_ = v_isSharedCheck_4603_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_snapshotTasks_4573_);
lean_inc(v_infoState_4572_);
lean_inc(v_messages_4571_);
lean_inc(v_cache_4570_);
lean_inc(v_traceState_4565_);
lean_inc(v_auxDeclNGen_4569_);
lean_inc(v_ngen_4568_);
lean_inc(v_nextMacroScope_4567_);
lean_inc(v_env_4566_);
lean_dec(v___x_4564_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4603_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
uint64_t v_tid_4577_; lean_object* v_traces_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4602_; 
v_tid_4577_ = lean_ctor_get_uint64(v_traceState_4565_, sizeof(void*)*1);
v_traces_4578_ = lean_ctor_get(v_traceState_4565_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_traceState_4565_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4580_ = v_traceState_4565_;
v_isShared_4581_ = v_isSharedCheck_4602_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_traces_4578_);
lean_dec(v_traceState_4565_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4602_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4582_; double v___x_4583_; uint8_t v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4592_; 
v___x_4582_ = lean_box(0);
v___x_4583_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4584_ = 0;
v___x_4585_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4586_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4586_, 0, v_cls_4551_);
lean_ctor_set(v___x_4586_, 1, v___x_4582_);
lean_ctor_set(v___x_4586_, 2, v___x_4585_);
lean_ctor_set_float(v___x_4586_, sizeof(void*)*3, v___x_4583_);
lean_ctor_set_float(v___x_4586_, sizeof(void*)*3 + 8, v___x_4583_);
lean_ctor_set_uint8(v___x_4586_, sizeof(void*)*3 + 16, v___x_4584_);
v___x_4587_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4588_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4586_);
lean_ctor_set(v___x_4588_, 1, v_a_4560_);
lean_ctor_set(v___x_4588_, 2, v___x_4587_);
lean_inc(v_ref_4558_);
v___x_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4589_, 0, v_ref_4558_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = l_Lean_PersistentArray_push___redArg(v_traces_4578_, v___x_4589_);
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v___x_4590_);
v___x_4592_ = v___x_4580_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4590_);
lean_ctor_set_uint64(v_reuseFailAlloc_4601_, sizeof(void*)*1, v_tid_4577_);
v___x_4592_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4594_; 
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 4, v___x_4592_);
v___x_4594_ = v___x_4575_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_env_4566_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_nextMacroScope_4567_);
lean_ctor_set(v_reuseFailAlloc_4600_, 2, v_ngen_4568_);
lean_ctor_set(v_reuseFailAlloc_4600_, 3, v_auxDeclNGen_4569_);
lean_ctor_set(v_reuseFailAlloc_4600_, 4, v___x_4592_);
lean_ctor_set(v_reuseFailAlloc_4600_, 5, v_cache_4570_);
lean_ctor_set(v_reuseFailAlloc_4600_, 6, v_messages_4571_);
lean_ctor_set(v_reuseFailAlloc_4600_, 7, v_infoState_4572_);
lean_ctor_set(v_reuseFailAlloc_4600_, 8, v_snapshotTasks_4573_);
v___x_4594_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4595_ = lean_st_ref_put(v___y_4556_, v___x_4594_);
v___x_4596_ = lean_box(0);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 0, v___x_4596_);
v___x_4598_ = v___x_4562_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4605_, lean_object* v_msg_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4605_, v_msg_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
return v_res_4612_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4615_ = l_Lean_stringToMessageData(v___x_4614_);
return v___x_4615_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4618_ = l_Lean_stringToMessageData(v___x_4617_);
return v___x_4618_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4621_ = l_Lean_stringToMessageData(v___x_4620_);
return v___x_4621_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4624_ = l_Lean_stringToMessageData(v___x_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4625_, lean_object* v_e_4626_, lean_object* v___x_4627_, lean_object* v___x_4628_, lean_object* v_cls_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = lean_st_mk_ref(v___x_4625_);
v___x_4636_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4626_, v___x_4627_, v___x_4635_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4708_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4639_ = v___x_4636_;
v_isShared_4640_ = v_isSharedCheck_4708_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4636_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4708_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4641_; lean_object* v_count_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4706_; 
v___x_4641_ = lean_st_ref_get(v___x_4635_);
lean_dec(v___x_4635_);
v_count_4642_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4706_ == 0)
{
lean_object* v_unused_4707_; 
v_unused_4707_ = lean_ctor_get(v___x_4641_, 1);
lean_dec(v_unused_4707_);
v___x_4644_ = v___x_4641_;
v_isShared_4645_ = v_isSharedCheck_4706_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_count_4642_);
lean_dec(v___x_4641_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4706_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
uint8_t v___x_4668_; 
v___x_4668_ = lean_nat_dec_eq(v_count_4642_, v___x_4628_);
if (v___x_4668_ == 0)
{
lean_object* v_toCold_4669_; lean_object* v_options_4670_; uint8_t v_hasTrace_4671_; 
v_toCold_4669_ = lean_ctor_get(v___y_4632_, 0);
v_options_4670_ = lean_ctor_get(v_toCold_4669_, 2);
v_hasTrace_4671_ = lean_ctor_get_uint8(v_options_4670_, sizeof(void*)*1);
if (v_hasTrace_4671_ == 0)
{
lean_dec(v_cls_4629_);
goto v___jp_4646_;
}
else
{
lean_object* v_inheritedTraceOptions_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v_inheritedTraceOptions_4672_ = lean_ctor_get(v_toCold_4669_, 11);
v___x_4673_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4629_);
v___x_4674_ = l_Lean_Name_append(v___x_4673_, v_cls_4629_);
v___x_4675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4672_, v_options_4670_, v___x_4674_);
lean_dec(v___x_4674_);
if (v___x_4675_ == 0)
{
lean_dec(v_cls_4629_);
goto v___jp_4646_;
}
else
{
lean_object* v_expr_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v_expr_4676_ = lean_ctor_get(v_a_4637_, 0);
v___x_4677_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4676_);
v___x_4678_ = l_Lean_indentExpr(v_expr_4676_);
v___x_4679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4677_);
lean_ctor_set(v___x_4679_, 1, v___x_4678_);
v___x_4680_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4629_, v___x_4679_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_dec_ref_known(v___x_4680_, 1);
goto v___jp_4646_;
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
lean_del_object(v___x_4644_);
lean_dec(v_count_4642_);
lean_del_object(v___x_4639_);
lean_dec(v_a_4637_);
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4680_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4680_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4689_; lean_object* v_options_4690_; uint8_t v_hasTrace_4691_; 
v_toCold_4689_ = lean_ctor_get(v___y_4632_, 0);
v_options_4690_ = lean_ctor_get(v_toCold_4689_, 2);
v_hasTrace_4691_ = lean_ctor_get_uint8(v_options_4690_, sizeof(void*)*1);
if (v_hasTrace_4691_ == 0)
{
lean_dec(v_cls_4629_);
goto v___jp_4646_;
}
else
{
lean_object* v_inheritedTraceOptions_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v_inheritedTraceOptions_4692_ = lean_ctor_get(v_toCold_4689_, 11);
v___x_4693_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4629_);
v___x_4694_ = l_Lean_Name_append(v___x_4693_, v_cls_4629_);
v___x_4695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4692_, v_options_4690_, v___x_4694_);
lean_dec(v___x_4694_);
if (v___x_4695_ == 0)
{
lean_dec(v_cls_4629_);
goto v___jp_4646_;
}
else
{
lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___x_4696_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4697_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4629_, v___x_4696_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_dec_ref_known(v___x_4697_, 1);
goto v___jp_4646_;
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_del_object(v___x_4644_);
lean_dec(v_count_4642_);
lean_del_object(v___x_4639_);
lean_dec(v_a_4637_);
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4697_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4697_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
}
}
v___jp_4646_:
{
lean_object* v_expr_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4666_; 
v_expr_4647_ = lean_ctor_get(v_a_4637_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v_a_4637_);
if (v_isSharedCheck_4666_ == 0)
{
lean_object* v_unused_4667_; 
v_unused_4667_ = lean_ctor_get(v_a_4637_, 1);
lean_dec(v_unused_4667_);
v___x_4649_ = v_a_4637_;
v_isShared_4650_ = v_isSharedCheck_4666_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_expr_4647_);
lean_dec(v_a_4637_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4666_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
v___x_4651_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4652_ = l_Nat_reprFast(v_count_4642_);
v___x_4653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
v___x_4654_ = l_Lean_MessageData_ofFormat(v___x_4653_);
if (v_isShared_4650_ == 0)
{
lean_ctor_set_tag(v___x_4649_, 7);
lean_ctor_set(v___x_4649_, 1, v___x_4654_);
lean_ctor_set(v___x_4649_, 0, v___x_4651_);
v___x_4656_ = v___x_4649_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v___x_4654_);
v___x_4656_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4657_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4645_ == 0)
{
lean_ctor_set_tag(v___x_4644_, 7);
lean_ctor_set(v___x_4644_, 1, v___x_4657_);
lean_ctor_set(v___x_4644_, 0, v___x_4656_);
v___x_4659_ = v___x_4644_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v_expr_4647_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v___x_4660_);
v___x_4662_ = v___x_4639_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4660_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
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
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
lean_dec(v___x_4635_);
lean_dec(v_cls_4629_);
v_a_4709_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4636_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4636_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4717_, lean_object* v_e_4718_, lean_object* v___x_4719_, lean_object* v___x_4720_, lean_object* v_cls_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4717_, v_e_4718_, v___x_4719_, v___x_4720_, v_cls_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___x_4720_);
lean_dec(v___x_4719_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4728_, lean_object* v_cache_4729_, lean_object* v_a_x3f_4730_){
_start:
{
lean_object* v___x_4732_; lean_object* v_mctx_4733_; lean_object* v_zetaDeltaFVarIds_4734_; lean_object* v_postponed_4735_; lean_object* v_diag_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4746_; 
v___x_4732_ = lean_st_ref_take(v___y_4728_);
v_mctx_4733_ = lean_ctor_get(v___x_4732_, 0);
v_zetaDeltaFVarIds_4734_ = lean_ctor_get(v___x_4732_, 2);
v_postponed_4735_ = lean_ctor_get(v___x_4732_, 3);
v_diag_4736_ = lean_ctor_get(v___x_4732_, 4);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4746_ == 0)
{
lean_object* v_unused_4747_; 
v_unused_4747_ = lean_ctor_get(v___x_4732_, 1);
lean_dec(v_unused_4747_);
v___x_4738_ = v___x_4732_;
v_isShared_4739_ = v_isSharedCheck_4746_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_diag_4736_);
lean_inc(v_postponed_4735_);
lean_inc(v_zetaDeltaFVarIds_4734_);
lean_inc(v_mctx_4733_);
lean_dec(v___x_4732_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4746_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 1, v_cache_4729_);
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_mctx_4733_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_cache_4729_);
lean_ctor_set(v_reuseFailAlloc_4745_, 2, v_zetaDeltaFVarIds_4734_);
lean_ctor_set(v_reuseFailAlloc_4745_, 3, v_postponed_4735_);
lean_ctor_set(v_reuseFailAlloc_4745_, 4, v_diag_4736_);
v___x_4741_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_st_ref_put(v___y_4728_, v___x_4741_);
v___x_4743_ = lean_box(0);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4748_, lean_object* v_cache_4749_, lean_object* v_a_x3f_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4748_, v_cache_4749_, v_a_x3f_4750_);
lean_dec(v_a_x3f_4750_);
lean_dec(v___y_4748_);
return v_res_4752_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0(void){
_start:
{
uint8_t v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = 2;
v___x_4754_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_4755_, lean_object* v___f_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___x_4807_; uint8_t v_beta_4808_; 
v___x_4807_ = l_Lean_Meta_Context_config(v___y_4757_);
v_beta_4808_ = lean_ctor_get_uint8(v___x_4807_, 13);
if (v_beta_4808_ == 0)
{
lean_dec_ref(v___x_4807_);
goto v___jp_4762_;
}
else
{
uint8_t v_iota_4809_; 
v_iota_4809_ = lean_ctor_get_uint8(v___x_4807_, 12);
if (v_iota_4809_ == 0)
{
lean_dec_ref(v___x_4807_);
goto v___jp_4762_;
}
else
{
uint8_t v_zeta_4810_; 
v_zeta_4810_ = lean_ctor_get_uint8(v___x_4807_, 15);
if (v_zeta_4810_ == 0)
{
lean_dec_ref(v___x_4807_);
goto v___jp_4762_;
}
else
{
uint8_t v_zetaHave_4811_; 
v_zetaHave_4811_ = lean_ctor_get_uint8(v___x_4807_, 18);
if (v_zetaHave_4811_ == 0)
{
lean_dec_ref(v___x_4807_);
goto v___jp_4762_;
}
else
{
uint8_t v_zetaDelta_4812_; 
v_zetaDelta_4812_ = lean_ctor_get_uint8(v___x_4807_, 16);
if (v_zetaDelta_4812_ == 0)
{
lean_dec_ref(v___x_4807_);
goto v___jp_4762_;
}
else
{
uint8_t v_etaStruct_4813_; uint8_t v_proj_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_etaStruct_4813_ = lean_ctor_get_uint8(v___x_4807_, 10);
v_proj_4814_ = lean_ctor_get_uint8(v___x_4807_, 14);
lean_dec_ref(v___x_4807_);
v___x_4815_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_4814_);
v___x_4816_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0);
v___x_4817_ = lean_nat_dec_eq(v___x_4815_, v___x_4816_);
lean_dec(v___x_4815_);
if (v___x_4817_ == 0)
{
goto v___jp_4762_;
}
else
{
uint8_t v___x_4818_; uint8_t v___x_4819_; 
v___x_4818_ = 0;
v___x_4819_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4813_, v___x_4818_);
if (v___x_4819_ == 0)
{
goto v___jp_4762_;
}
else
{
lean_object* v___x_4820_; 
v___x_4820_ = lean_apply_5(v___f_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, lean_box(0));
return v___x_4820_;
}
}
}
}
}
}
}
v___jp_4762_:
{
lean_object* v___x_4763_; uint8_t v_foApprox_4764_; uint8_t v_ctxApprox_4765_; uint8_t v_quasiPatternApprox_4766_; uint8_t v_constApprox_4767_; uint8_t v_isDefEqStuckEx_4768_; uint8_t v_unificationHints_4769_; uint8_t v_proofIrrelevance_4770_; uint8_t v_assignSyntheticOpaque_4771_; uint8_t v_offsetCnstrs_4772_; uint8_t v_transparency_4773_; uint8_t v_univApprox_4774_; uint8_t v_zetaUnused_4775_; uint8_t v_canUnfoldPredicateConfig_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4806_; 
v___x_4763_ = l_Lean_Meta_Context_config(v___y_4757_);
v_foApprox_4764_ = lean_ctor_get_uint8(v___x_4763_, 0);
v_ctxApprox_4765_ = lean_ctor_get_uint8(v___x_4763_, 1);
v_quasiPatternApprox_4766_ = lean_ctor_get_uint8(v___x_4763_, 2);
v_constApprox_4767_ = lean_ctor_get_uint8(v___x_4763_, 3);
v_isDefEqStuckEx_4768_ = lean_ctor_get_uint8(v___x_4763_, 4);
v_unificationHints_4769_ = lean_ctor_get_uint8(v___x_4763_, 5);
v_proofIrrelevance_4770_ = lean_ctor_get_uint8(v___x_4763_, 6);
v_assignSyntheticOpaque_4771_ = lean_ctor_get_uint8(v___x_4763_, 7);
v_offsetCnstrs_4772_ = lean_ctor_get_uint8(v___x_4763_, 8);
v_transparency_4773_ = lean_ctor_get_uint8(v___x_4763_, 9);
v_univApprox_4774_ = lean_ctor_get_uint8(v___x_4763_, 11);
v_zetaUnused_4775_ = lean_ctor_get_uint8(v___x_4763_, 17);
v_canUnfoldPredicateConfig_4776_ = lean_ctor_get_uint8(v___x_4763_, 19);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4778_ = v___x_4763_;
v_isShared_4779_ = v_isSharedCheck_4806_;
goto v_resetjp_4777_;
}
else
{
lean_dec(v___x_4763_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4806_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
uint8_t v___x_4780_; uint8_t v___x_4781_; lean_object* v___x_4783_; 
v___x_4780_ = 0;
v___x_4781_ = 2;
if (v_isShared_4779_ == 0)
{
v___x_4783_ = v___x_4778_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 0, v_foApprox_4764_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 1, v_ctxApprox_4765_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 2, v_quasiPatternApprox_4766_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 3, v_constApprox_4767_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 4, v_isDefEqStuckEx_4768_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 5, v_unificationHints_4769_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 6, v_proofIrrelevance_4770_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 7, v_assignSyntheticOpaque_4771_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 8, v_offsetCnstrs_4772_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 9, v_transparency_4773_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 11, v_univApprox_4774_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 17, v_zetaUnused_4775_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, 19, v_canUnfoldPredicateConfig_4776_);
v___x_4783_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
uint8_t v_trackZetaDelta_4784_; lean_object* v_zetaDeltaSet_4785_; lean_object* v_lctx_4786_; lean_object* v_localInstances_4787_; lean_object* v_defEqCtx_x3f_4788_; lean_object* v_synthPendingDepth_4789_; lean_object* v_customCanUnfoldPredicate_x3f_4790_; uint8_t v_univApprox_4791_; uint8_t v_inTypeClassResolution_4792_; uint8_t v_cacheInferType_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4803_; 
lean_ctor_set_uint8(v___x_4783_, 10, v___x_4780_);
lean_ctor_set_uint8(v___x_4783_, 12, v___x_4755_);
lean_ctor_set_uint8(v___x_4783_, 13, v___x_4755_);
lean_ctor_set_uint8(v___x_4783_, 14, v___x_4781_);
lean_ctor_set_uint8(v___x_4783_, 15, v___x_4755_);
lean_ctor_set_uint8(v___x_4783_, 16, v___x_4755_);
lean_ctor_set_uint8(v___x_4783_, 18, v___x_4755_);
v_trackZetaDelta_4784_ = lean_ctor_get_uint8(v___y_4757_, sizeof(void*)*7);
v_zetaDeltaSet_4785_ = lean_ctor_get(v___y_4757_, 1);
v_lctx_4786_ = lean_ctor_get(v___y_4757_, 2);
v_localInstances_4787_ = lean_ctor_get(v___y_4757_, 3);
v_defEqCtx_x3f_4788_ = lean_ctor_get(v___y_4757_, 4);
v_synthPendingDepth_4789_ = lean_ctor_get(v___y_4757_, 5);
v_customCanUnfoldPredicate_x3f_4790_ = lean_ctor_get(v___y_4757_, 6);
v_univApprox_4791_ = lean_ctor_get_uint8(v___y_4757_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4792_ = lean_ctor_get_uint8(v___y_4757_, sizeof(void*)*7 + 2);
v_cacheInferType_4793_ = lean_ctor_get_uint8(v___y_4757_, sizeof(void*)*7 + 3);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___y_4757_);
if (v_isSharedCheck_4803_ == 0)
{
lean_object* v_unused_4804_; 
v_unused_4804_ = lean_ctor_get(v___y_4757_, 0);
lean_dec(v_unused_4804_);
v___x_4795_ = v___y_4757_;
v_isShared_4796_ = v_isSharedCheck_4803_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4790_);
lean_inc(v_synthPendingDepth_4789_);
lean_inc(v_defEqCtx_x3f_4788_);
lean_inc(v_localInstances_4787_);
lean_inc(v_lctx_4786_);
lean_inc(v_zetaDeltaSet_4785_);
lean_dec(v___y_4757_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4803_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
uint64_t v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4797_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4783_);
v___x_4798_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4798_, 0, v___x_4783_);
lean_ctor_set_uint64(v___x_4798_, sizeof(void*)*1, v___x_4797_);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 0, v___x_4798_);
v___x_4800_ = v___x_4795_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4798_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v_zetaDeltaSet_4785_);
lean_ctor_set(v_reuseFailAlloc_4802_, 2, v_lctx_4786_);
lean_ctor_set(v_reuseFailAlloc_4802_, 3, v_localInstances_4787_);
lean_ctor_set(v_reuseFailAlloc_4802_, 4, v_defEqCtx_x3f_4788_);
lean_ctor_set(v_reuseFailAlloc_4802_, 5, v_synthPendingDepth_4789_);
lean_ctor_set(v_reuseFailAlloc_4802_, 6, v_customCanUnfoldPredicate_x3f_4790_);
lean_ctor_set_uint8(v_reuseFailAlloc_4802_, sizeof(void*)*7, v_trackZetaDelta_4784_);
lean_ctor_set_uint8(v_reuseFailAlloc_4802_, sizeof(void*)*7 + 1, v_univApprox_4791_);
lean_ctor_set_uint8(v_reuseFailAlloc_4802_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4792_);
lean_ctor_set_uint8(v_reuseFailAlloc_4802_, sizeof(void*)*7 + 3, v_cacheInferType_4793_);
v___x_4800_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4801_; 
v___x_4801_ = lean_apply_5(v___f_4756_, v___x_4800_, v___y_4758_, v___y_4759_, v___y_4760_, lean_box(0));
return v___x_4801_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_4821_, lean_object* v___f_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
uint8_t v___x_14004__boxed_4828_; lean_object* v_res_4829_; 
v___x_14004__boxed_4828_ = lean_unbox(v___x_4821_);
v_res_4829_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_14004__boxed_4828_, v___f_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
return v_res_4829_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1));
v___x_4834_ = l_Lean_MessageData_ofFormat(v___x_4833_);
return v___x_4834_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3(void){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4835_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___x_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
return v___x_4837_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4839_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4838_);
lean_ctor_set(v___x_4839_, 1, v___x_4838_);
lean_ctor_set(v___x_4839_, 2, v___x_4838_);
lean_ctor_set(v___x_4839_, 3, v___x_4838_);
lean_ctor_set(v___x_4839_, 4, v___x_4838_);
lean_ctor_set(v___x_4839_, 5, v___x_4838_);
return v___x_4839_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6(void){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4841_ = lean_unsigned_to_nat(0u);
v___x_4842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
lean_ctor_set(v___x_4842_, 1, v___x_4840_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_4843_, lean_object* v_e_4844_, lean_object* v_cls_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
if (v___x_4843_ == 0)
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
lean_dec(v_cls_4845_);
v___x_4851_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4852_, 0, v_e_4844_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
v___x_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
return v___x_4853_;
}
else
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v_mctx_4856_; lean_object* v_zetaDeltaFVarIds_4857_; lean_object* v_postponed_4858_; lean_object* v_diag_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4956_; 
v___x_4854_ = lean_st_ref_get(v___y_4847_);
v___x_4855_ = lean_st_ref_take(v___y_4847_);
v_mctx_4856_ = lean_ctor_get(v___x_4855_, 0);
v_zetaDeltaFVarIds_4857_ = lean_ctor_get(v___x_4855_, 2);
v_postponed_4858_ = lean_ctor_get(v___x_4855_, 3);
v_diag_4859_ = lean_ctor_get(v___x_4855_, 4);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4956_ == 0)
{
lean_object* v_unused_4957_; 
v_unused_4957_ = lean_ctor_get(v___x_4855_, 1);
lean_dec(v_unused_4957_);
v___x_4861_ = v___x_4855_;
v_isShared_4862_ = v_isSharedCheck_4956_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_diag_4859_);
lean_inc(v_postponed_4858_);
lean_inc(v_zetaDeltaFVarIds_4857_);
lean_inc(v_mctx_4856_);
lean_dec(v___x_4855_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4956_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4863_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 1, v___x_4863_);
v___x_4865_ = v___x_4861_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_mctx_4856_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4955_, 2, v_zetaDeltaFVarIds_4857_);
lean_ctor_set(v_reuseFailAlloc_4955_, 3, v_postponed_4858_);
lean_ctor_set(v_reuseFailAlloc_4955_, 4, v_diag_4859_);
v___x_4865_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v_mctx_4868_; lean_object* v_cache_4869_; lean_object* v_zetaDeltaFVarIds_4870_; lean_object* v_postponed_4871_; lean_object* v_diag_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4954_; 
v___x_4866_ = lean_st_ref_put(v___y_4847_, v___x_4865_);
v___x_4867_ = lean_st_ref_take(v___y_4847_);
v_mctx_4868_ = lean_ctor_get(v___x_4867_, 0);
v_cache_4869_ = lean_ctor_get(v___x_4867_, 1);
v_zetaDeltaFVarIds_4870_ = lean_ctor_get(v___x_4867_, 2);
v_postponed_4871_ = lean_ctor_get(v___x_4867_, 3);
v_diag_4872_ = lean_ctor_get(v___x_4867_, 4);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4874_ = v___x_4867_;
v_isShared_4875_ = v_isSharedCheck_4954_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_diag_4872_);
lean_inc(v_postponed_4871_);
lean_inc(v_zetaDeltaFVarIds_4870_);
lean_inc(v_cache_4869_);
lean_inc(v_mctx_4868_);
lean_dec(v___x_4867_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4954_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; lean_object* v___x_4878_; 
v___x_4876_ = lean_box(1);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 2, v___x_4876_);
v___x_4878_ = v___x_4874_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_mctx_4868_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v_cache_4869_);
lean_ctor_set(v_reuseFailAlloc_4953_, 2, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4953_, 3, v_postponed_4871_);
lean_ctor_set(v_reuseFailAlloc_4953_, 4, v_diag_4872_);
v___x_4878_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4879_; lean_object* v_cache_4880_; lean_object* v_keyedConfig_4881_; lean_object* v_zetaDeltaSet_4882_; lean_object* v_lctx_4883_; lean_object* v_localInstances_4884_; lean_object* v_defEqCtx_x3f_4885_; lean_object* v_synthPendingDepth_4886_; lean_object* v_customCanUnfoldPredicate_x3f_4887_; uint8_t v_univApprox_4888_; uint8_t v_inTypeClassResolution_4889_; uint8_t v_cacheInferType_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; uint8_t v_transparency_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___f_4898_; lean_object* v_a_4900_; lean_object* v_a_4912_; lean_object* v_a_4925_; lean_object* v___y_4929_; lean_object* v___y_4933_; uint8_t v___x_4936_; 
v___x_4879_ = lean_st_ref_put(v___y_4847_, v___x_4878_);
v_cache_4880_ = lean_ctor_get(v___x_4854_, 1);
lean_inc_ref(v_cache_4880_);
lean_dec(v___x_4854_);
v_keyedConfig_4881_ = lean_ctor_get(v___y_4846_, 0);
v_zetaDeltaSet_4882_ = lean_ctor_get(v___y_4846_, 1);
v_lctx_4883_ = lean_ctor_get(v___y_4846_, 2);
v_localInstances_4884_ = lean_ctor_get(v___y_4846_, 3);
v_defEqCtx_x3f_4885_ = lean_ctor_get(v___y_4846_, 4);
v_synthPendingDepth_4886_ = lean_ctor_get(v___y_4846_, 5);
v_customCanUnfoldPredicate_x3f_4887_ = lean_ctor_get(v___y_4846_, 6);
v_univApprox_4888_ = lean_ctor_get_uint8(v___y_4846_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4889_ = lean_ctor_get_uint8(v___y_4846_, sizeof(void*)*7 + 2);
v_cacheInferType_4890_ = lean_ctor_get_uint8(v___y_4846_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_4887_);
lean_inc(v_synthPendingDepth_4886_);
lean_inc(v_defEqCtx_x3f_4885_);
lean_inc_ref(v_localInstances_4884_);
lean_inc_ref(v_lctx_4883_);
lean_inc(v_zetaDeltaSet_4882_);
lean_inc_ref(v_keyedConfig_4881_);
v___x_4891_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4891_, 0, v_keyedConfig_4881_);
lean_ctor_set(v___x_4891_, 1, v_zetaDeltaSet_4882_);
lean_ctor_set(v___x_4891_, 2, v_lctx_4883_);
lean_ctor_set(v___x_4891_, 3, v_localInstances_4884_);
lean_ctor_set(v___x_4891_, 4, v_defEqCtx_x3f_4885_);
lean_ctor_set(v___x_4891_, 5, v_synthPendingDepth_4886_);
lean_ctor_set(v___x_4891_, 6, v_customCanUnfoldPredicate_x3f_4887_);
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*7, v___x_4843_);
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*7 + 1, v_univApprox_4888_);
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4889_);
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*7 + 3, v_cacheInferType_4890_);
v___x_4892_ = l_Lean_Meta_Context_config(v___x_4891_);
v_transparency_4893_ = lean_ctor_get_uint8(v___x_4892_, 9);
lean_dec_ref(v___x_4892_);
v___x_4894_ = lean_unsigned_to_nat(0u);
v___x_4895_ = 0;
v___x_4896_ = lean_box(0);
v___x_4897_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
v___f_4898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4898_, 0, v___x_4897_);
lean_closure_set(v___f_4898_, 1, v_e_4844_);
lean_closure_set(v___f_4898_, 2, v___x_4896_);
lean_closure_set(v___f_4898_, 3, v___x_4894_);
lean_closure_set(v___f_4898_, 4, v_cls_4845_);
v___x_4936_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4893_, v___x_4895_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; uint8_t v_transparency_4940_; uint8_t v___x_4941_; uint8_t v___x_4942_; 
lean_dec_ref_known(v___x_4891_, 7);
lean_inc_ref(v_keyedConfig_4881_);
v___x_4937_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4895_, v_keyedConfig_4881_);
lean_inc(v_customCanUnfoldPredicate_x3f_4887_);
lean_inc(v_synthPendingDepth_4886_);
lean_inc(v_defEqCtx_x3f_4885_);
lean_inc_ref(v_localInstances_4884_);
lean_inc_ref(v_lctx_4883_);
lean_inc(v_zetaDeltaSet_4882_);
lean_inc_ref(v___x_4937_);
v___x_4938_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
lean_ctor_set(v___x_4938_, 1, v_zetaDeltaSet_4882_);
lean_ctor_set(v___x_4938_, 2, v_lctx_4883_);
lean_ctor_set(v___x_4938_, 3, v_localInstances_4884_);
lean_ctor_set(v___x_4938_, 4, v_defEqCtx_x3f_4885_);
lean_ctor_set(v___x_4938_, 5, v_synthPendingDepth_4886_);
lean_ctor_set(v___x_4938_, 6, v_customCanUnfoldPredicate_x3f_4887_);
lean_ctor_set_uint8(v___x_4938_, sizeof(void*)*7, v___x_4843_);
lean_ctor_set_uint8(v___x_4938_, sizeof(void*)*7 + 1, v_univApprox_4888_);
lean_ctor_set_uint8(v___x_4938_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4889_);
lean_ctor_set_uint8(v___x_4938_, sizeof(void*)*7 + 3, v_cacheInferType_4890_);
v___x_4939_ = l_Lean_Meta_Context_config(v___x_4938_);
v_transparency_4940_ = lean_ctor_get_uint8(v___x_4939_, 9);
lean_dec_ref(v___x_4939_);
v___x_4941_ = 1;
v___x_4942_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4940_, v___x_4941_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; 
lean_dec_ref(v___x_4937_);
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
lean_inc(v___y_4847_);
v___x_4943_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4843_, v___f_4898_, v___x_4938_, v___y_4847_, v___y_4848_, v___y_4849_);
v___y_4933_ = v___x_4943_;
goto v___jp_4932_;
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
lean_dec_ref_known(v___x_4938_, 7);
v___x_4944_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4941_, v___x_4937_);
lean_inc(v_customCanUnfoldPredicate_x3f_4887_);
lean_inc(v_synthPendingDepth_4886_);
lean_inc(v_defEqCtx_x3f_4885_);
lean_inc_ref(v_localInstances_4884_);
lean_inc_ref(v_lctx_4883_);
lean_inc(v_zetaDeltaSet_4882_);
v___x_4945_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
lean_ctor_set(v___x_4945_, 1, v_zetaDeltaSet_4882_);
lean_ctor_set(v___x_4945_, 2, v_lctx_4883_);
lean_ctor_set(v___x_4945_, 3, v_localInstances_4884_);
lean_ctor_set(v___x_4945_, 4, v_defEqCtx_x3f_4885_);
lean_ctor_set(v___x_4945_, 5, v_synthPendingDepth_4886_);
lean_ctor_set(v___x_4945_, 6, v_customCanUnfoldPredicate_x3f_4887_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*7, v___x_4843_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*7 + 1, v_univApprox_4888_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4889_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*7 + 3, v_cacheInferType_4890_);
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
lean_inc(v___y_4847_);
v___x_4946_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4843_, v___f_4898_, v___x_4945_, v___y_4847_, v___y_4848_, v___y_4849_);
v___y_4933_ = v___x_4946_;
goto v___jp_4932_;
}
}
else
{
uint8_t v___x_4947_; uint8_t v___x_4948_; 
v___x_4947_ = 1;
v___x_4948_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4893_, v___x_4947_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; 
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
lean_inc(v___y_4847_);
v___x_4949_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4936_, v___f_4898_, v___x_4891_, v___y_4847_, v___y_4848_, v___y_4849_);
v___y_4929_ = v___x_4949_;
goto v___jp_4928_;
}
else
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
lean_dec_ref_known(v___x_4891_, 7);
lean_inc_ref(v_keyedConfig_4881_);
v___x_4950_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4947_, v_keyedConfig_4881_);
lean_inc(v_customCanUnfoldPredicate_x3f_4887_);
lean_inc(v_synthPendingDepth_4886_);
lean_inc(v_defEqCtx_x3f_4885_);
lean_inc_ref(v_localInstances_4884_);
lean_inc_ref(v_lctx_4883_);
lean_inc(v_zetaDeltaSet_4882_);
v___x_4951_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
lean_ctor_set(v___x_4951_, 1, v_zetaDeltaSet_4882_);
lean_ctor_set(v___x_4951_, 2, v_lctx_4883_);
lean_ctor_set(v___x_4951_, 3, v_localInstances_4884_);
lean_ctor_set(v___x_4951_, 4, v_defEqCtx_x3f_4885_);
lean_ctor_set(v___x_4951_, 5, v_synthPendingDepth_4886_);
lean_ctor_set(v___x_4951_, 6, v_customCanUnfoldPredicate_x3f_4887_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7, v___x_4843_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7 + 1, v_univApprox_4888_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4889_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7 + 3, v_cacheInferType_4890_);
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
lean_inc(v___y_4847_);
v___x_4952_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4936_, v___f_4898_, v___x_4951_, v___y_4847_, v___y_4848_, v___y_4849_);
v___y_4929_ = v___x_4952_;
goto v___jp_4928_;
}
}
v___jp_4899_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
v___x_4901_ = lean_box(0);
v___x_4902_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4847_, v_cache_4880_, v___x_4901_);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4909_ == 0)
{
lean_object* v_unused_4910_; 
v_unused_4910_ = lean_ctor_get(v___x_4902_, 0);
lean_dec(v_unused_4910_);
v___x_4904_ = v___x_4902_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_dec(v___x_4902_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
lean_ctor_set_tag(v___x_4904_, 1);
lean_ctor_set(v___x_4904_, 0, v_a_4900_);
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4900_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
v___jp_4911_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_inc(v_a_4912_);
v___x_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4913_, 0, v_a_4912_);
v___x_4914_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4847_, v_zetaDeltaFVarIds_4870_, v___x_4913_);
lean_dec_ref(v___x_4914_);
v___x_4915_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4847_, v_cache_4880_, v___x_4913_);
lean_dec_ref_known(v___x_4913_, 1);
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
lean_ctor_set(v___x_4917_, 0, v_a_4912_);
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4912_);
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
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = lean_box(0);
v___x_4927_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4847_, v_zetaDeltaFVarIds_4870_, v___x_4926_);
lean_dec_ref(v___x_4927_);
v_a_4900_ = v_a_4925_;
goto v___jp_4899_;
}
v___jp_4928_:
{
if (lean_obj_tag(v___y_4929_) == 0)
{
lean_object* v_a_4930_; 
v_a_4930_ = lean_ctor_get(v___y_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___y_4929_, 1);
v_a_4912_ = v_a_4930_;
goto v___jp_4911_;
}
else
{
lean_object* v_a_4931_; 
v_a_4931_ = lean_ctor_get(v___y_4929_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___y_4929_, 1);
v_a_4925_ = v_a_4931_;
goto v___jp_4924_;
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
v_a_4912_ = v_a_4934_;
goto v___jp_4911_;
}
else
{
lean_object* v_a_4935_; 
v_a_4935_ = lean_ctor_get(v___y_4933_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___y_4933_, 1);
v_a_4925_ = v_a_4935_;
goto v___jp_4924_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_4958_, lean_object* v_e_4959_, lean_object* v_cls_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
uint8_t v___x_14127__boxed_4966_; lean_object* v_res_4967_; 
v___x_14127__boxed_4966_ = lean_unbox(v___x_4958_);
v_res_4967_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14127__boxed_4966_, v_e_4959_, v_cls_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_){
_start:
{
if (lean_obj_tag(v_x_4968_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4982_; 
v_a_4974_ = lean_ctor_get(v_x_4968_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v_x_4968_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4976_ = v_x_4968_;
v_isShared_4977_ = v_isSharedCheck_4982_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v_x_4968_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4982_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4978_; lean_object* v___x_4980_; 
v___x_4978_ = l_Lean_Exception_toMessageData(v_a_4974_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v___x_4978_);
v___x_4980_ = v___x_4976_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4978_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
else
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4991_; 
v_a_4983_ = lean_ctor_get(v_x_4968_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v_x_4968_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4985_ = v_x_4968_;
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v_x_4968_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v_snd_4987_; lean_object* v___x_4989_; 
v_snd_4987_ = lean_ctor_get(v_a_4983_, 1);
lean_inc(v_snd_4987_);
lean_dec(v_a_4983_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set_tag(v___x_4985_, 0);
lean_ctor_set(v___x_4985_, 0, v_snd_4987_);
v___x_4989_ = v___x_4985_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_snd_4987_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_4999_){
_start:
{
if (lean_obj_tag(v_x_4999_) == 0)
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
v_a_5001_ = lean_ctor_get(v_x_4999_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v_x_4999_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v_x_4999_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v_x_4999_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
lean_ctor_set_tag(v___x_5003_, 1);
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
v_a_5009_ = lean_ctor_get(v_x_4999_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v_x_4999_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v_x_4999_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v_x_4999_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
lean_ctor_set_tag(v___x_5011_, 0);
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5017_);
return v_res_5019_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5020_){
_start:
{
if (lean_obj_tag(v_e_5020_) == 0)
{
uint8_t v___x_5021_; 
v___x_5021_ = 2;
return v___x_5021_;
}
else
{
uint8_t v___x_5022_; 
v___x_5022_ = 0;
return v___x_5022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5023_){
_start:
{
uint8_t v_res_5024_; lean_object* v_r_5025_; 
v_res_5024_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5023_);
lean_dec_ref(v_e_5023_);
v_r_5025_ = lean_box(v_res_5024_);
return v_r_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5026_, lean_object* v_data_5027_, lean_object* v_ref_5028_, lean_object* v_msg_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_toCold_5035_; lean_object* v_currRecDepth_5036_; lean_object* v_ref_5037_; uint8_t v_diag_5038_; uint8_t v_suppressElabErrors_5039_; lean_object* v___x_5040_; lean_object* v_traceState_5041_; lean_object* v_traces_5042_; lean_object* v_ref_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; size_t v_sz_5046_; size_t v___x_5047_; lean_object* v___x_5048_; lean_object* v_msg_5049_; lean_object* v___x_5050_; lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5088_; 
v_toCold_5035_ = lean_ctor_get(v___y_5032_, 0);
v_currRecDepth_5036_ = lean_ctor_get(v___y_5032_, 1);
v_ref_5037_ = lean_ctor_get(v___y_5032_, 2);
v_diag_5038_ = lean_ctor_get_uint8(v___y_5032_, sizeof(void*)*3);
v_suppressElabErrors_5039_ = lean_ctor_get_uint8(v___y_5032_, sizeof(void*)*3 + 1);
v___x_5040_ = lean_st_ref_get(v___y_5033_);
v_traceState_5041_ = lean_ctor_get(v___x_5040_, 4);
lean_inc_ref(v_traceState_5041_);
lean_dec(v___x_5040_);
v_traces_5042_ = lean_ctor_get(v_traceState_5041_, 0);
lean_inc_ref(v_traces_5042_);
lean_dec_ref(v_traceState_5041_);
v_ref_5043_ = l_Lean_replaceRef(v_ref_5028_, v_ref_5037_);
lean_inc(v_currRecDepth_5036_);
lean_inc_ref(v_toCold_5035_);
v___x_5044_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5044_, 0, v_toCold_5035_);
lean_ctor_set(v___x_5044_, 1, v_currRecDepth_5036_);
lean_ctor_set(v___x_5044_, 2, v_ref_5043_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*3, v_diag_5038_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*3 + 1, v_suppressElabErrors_5039_);
v___x_5045_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5042_);
lean_dec_ref(v_traces_5042_);
v_sz_5046_ = lean_array_size(v___x_5045_);
v___x_5047_ = ((size_t)0ULL);
v___x_5048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5046_, v___x_5047_, v___x_5045_);
v_msg_5049_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5049_, 0, v_data_5027_);
lean_ctor_set(v_msg_5049_, 1, v_msg_5029_);
lean_ctor_set(v_msg_5049_, 2, v___x_5048_);
v___x_5050_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5049_, v___y_5030_, v___y_5031_, v___x_5044_, v___y_5033_);
lean_dec_ref_known(v___x_5044_, 3);
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5053_ = v___x_5050_;
v_isShared_5054_ = v_isSharedCheck_5088_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_dec(v___x_5050_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5088_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5055_; lean_object* v_traceState_5056_; lean_object* v_env_5057_; lean_object* v_nextMacroScope_5058_; lean_object* v_ngen_5059_; lean_object* v_auxDeclNGen_5060_; lean_object* v_cache_5061_; lean_object* v_messages_5062_; lean_object* v_infoState_5063_; lean_object* v_snapshotTasks_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5087_; 
v___x_5055_ = lean_st_ref_take(v___y_5033_);
v_traceState_5056_ = lean_ctor_get(v___x_5055_, 4);
v_env_5057_ = lean_ctor_get(v___x_5055_, 0);
v_nextMacroScope_5058_ = lean_ctor_get(v___x_5055_, 1);
v_ngen_5059_ = lean_ctor_get(v___x_5055_, 2);
v_auxDeclNGen_5060_ = lean_ctor_get(v___x_5055_, 3);
v_cache_5061_ = lean_ctor_get(v___x_5055_, 5);
v_messages_5062_ = lean_ctor_get(v___x_5055_, 6);
v_infoState_5063_ = lean_ctor_get(v___x_5055_, 7);
v_snapshotTasks_5064_ = lean_ctor_get(v___x_5055_, 8);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5066_ = v___x_5055_;
v_isShared_5067_ = v_isSharedCheck_5087_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_snapshotTasks_5064_);
lean_inc(v_infoState_5063_);
lean_inc(v_messages_5062_);
lean_inc(v_cache_5061_);
lean_inc(v_traceState_5056_);
lean_inc(v_auxDeclNGen_5060_);
lean_inc(v_ngen_5059_);
lean_inc(v_nextMacroScope_5058_);
lean_inc(v_env_5057_);
lean_dec(v___x_5055_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5087_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
uint64_t v_tid_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5085_; 
v_tid_5068_ = lean_ctor_get_uint64(v_traceState_5056_, sizeof(void*)*1);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_traceState_5056_);
if (v_isSharedCheck_5085_ == 0)
{
lean_object* v_unused_5086_; 
v_unused_5086_ = lean_ctor_get(v_traceState_5056_, 0);
lean_dec(v_unused_5086_);
v___x_5070_ = v_traceState_5056_;
v_isShared_5071_ = v_isSharedCheck_5085_;
goto v_resetjp_5069_;
}
else
{
lean_dec(v_traceState_5056_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5085_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5072_, 0, v_ref_5028_);
lean_ctor_set(v___x_5072_, 1, v_a_5051_);
v___x_5073_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5026_, v___x_5072_);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v___x_5073_);
v___x_5075_ = v___x_5070_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5073_);
lean_ctor_set_uint64(v_reuseFailAlloc_5084_, sizeof(void*)*1, v_tid_5068_);
v___x_5075_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5077_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 4, v___x_5075_);
v___x_5077_ = v___x_5066_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_env_5057_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_nextMacroScope_5058_);
lean_ctor_set(v_reuseFailAlloc_5083_, 2, v_ngen_5059_);
lean_ctor_set(v_reuseFailAlloc_5083_, 3, v_auxDeclNGen_5060_);
lean_ctor_set(v_reuseFailAlloc_5083_, 4, v___x_5075_);
lean_ctor_set(v_reuseFailAlloc_5083_, 5, v_cache_5061_);
lean_ctor_set(v_reuseFailAlloc_5083_, 6, v_messages_5062_);
lean_ctor_set(v_reuseFailAlloc_5083_, 7, v_infoState_5063_);
lean_ctor_set(v_reuseFailAlloc_5083_, 8, v_snapshotTasks_5064_);
v___x_5077_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5081_; 
v___x_5078_ = lean_st_ref_put(v___y_5033_, v___x_5077_);
v___x_5079_ = lean_box(0);
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 0, v___x_5079_);
v___x_5081_ = v___x_5053_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5079_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5089_, lean_object* v_data_5090_, lean_object* v_ref_5091_, lean_object* v_msg_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5089_, v_data_5090_, v_ref_5091_, v_msg_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5099_, uint8_t v_collapsed_5100_, lean_object* v_tag_5101_, lean_object* v_opts_5102_, uint8_t v_clsEnabled_5103_, lean_object* v_oldTraces_5104_, lean_object* v_msg_5105_, lean_object* v_resStartStop_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_fst_5112_; lean_object* v_snd_5113_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v_data_5117_; lean_object* v_fst_5128_; lean_object* v_snd_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; lean_object* v___y_5133_; lean_object* v_a_5134_; uint8_t v___y_5149_; double v___y_5180_; 
v_fst_5112_ = lean_ctor_get(v_resStartStop_5106_, 0);
lean_inc(v_fst_5112_);
v_snd_5113_ = lean_ctor_get(v_resStartStop_5106_, 1);
lean_inc(v_snd_5113_);
lean_dec_ref(v_resStartStop_5106_);
v_fst_5128_ = lean_ctor_get(v_snd_5113_, 0);
lean_inc(v_fst_5128_);
v_snd_5129_ = lean_ctor_get(v_snd_5113_, 1);
lean_inc(v_snd_5129_);
lean_dec(v_snd_5113_);
v___x_5130_ = l_Lean_trace_profiler;
v___x_5131_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5102_, v___x_5130_);
if (v___x_5131_ == 0)
{
v___y_5149_ = v___x_5131_;
goto v___jp_5148_;
}
else
{
lean_object* v___x_5185_; uint8_t v___x_5186_; 
v___x_5185_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5186_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5102_, v___x_5185_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; lean_object* v___x_5188_; double v___x_5189_; double v___x_5190_; double v___x_5191_; 
v___x_5187_ = l_Lean_trace_profiler_threshold;
v___x_5188_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5102_, v___x_5187_);
v___x_5189_ = lean_float_of_nat(v___x_5188_);
v___x_5190_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5191_ = lean_float_div(v___x_5189_, v___x_5190_);
v___y_5180_ = v___x_5191_;
goto v___jp_5179_;
}
else
{
lean_object* v___x_5192_; lean_object* v___x_5193_; double v___x_5194_; 
v___x_5192_ = l_Lean_trace_profiler_threshold;
v___x_5193_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5102_, v___x_5192_);
v___x_5194_ = lean_float_of_nat(v___x_5193_);
v___y_5180_ = v___x_5194_;
goto v___jp_5179_;
}
}
v___jp_5114_:
{
lean_object* v___x_5118_; 
lean_inc(v___y_5115_);
v___x_5118_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5104_, v_data_5117_, v___y_5115_, v___y_5116_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v___x_5119_; 
lean_dec_ref_known(v___x_5118_, 1);
v___x_5119_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5112_);
return v___x_5119_;
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
lean_dec(v_fst_5112_);
v_a_5120_ = lean_ctor_get(v___x_5118_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5118_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5118_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5118_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5125_; 
if (v_isShared_5123_ == 0)
{
v___x_5125_ = v___x_5122_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
}
}
}
}
v___jp_5132_:
{
uint8_t v_result_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; double v___x_5138_; lean_object* v_data_5139_; 
v_result_5135_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5112_);
v___x_5136_ = lean_box(v_result_5135_);
v___x_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
v___x_5138_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5101_);
lean_inc_ref(v___x_5137_);
lean_inc(v_cls_5099_);
v_data_5139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5139_, 0, v_cls_5099_);
lean_ctor_set(v_data_5139_, 1, v___x_5137_);
lean_ctor_set(v_data_5139_, 2, v_tag_5101_);
lean_ctor_set_float(v_data_5139_, sizeof(void*)*3, v___x_5138_);
lean_ctor_set_float(v_data_5139_, sizeof(void*)*3 + 8, v___x_5138_);
lean_ctor_set_uint8(v_data_5139_, sizeof(void*)*3 + 16, v_collapsed_5100_);
if (v___x_5131_ == 0)
{
lean_dec_ref_known(v___x_5137_, 1);
lean_dec(v_snd_5129_);
lean_dec(v_fst_5128_);
lean_dec_ref(v_tag_5101_);
lean_dec(v_cls_5099_);
v___y_5115_ = v___y_5133_;
v___y_5116_ = v_a_5134_;
v_data_5117_ = v_data_5139_;
goto v___jp_5114_;
}
else
{
lean_object* v_data_5140_; double v___x_5141_; double v___x_5142_; 
lean_dec_ref_known(v_data_5139_, 3);
v_data_5140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5140_, 0, v_cls_5099_);
lean_ctor_set(v_data_5140_, 1, v___x_5137_);
lean_ctor_set(v_data_5140_, 2, v_tag_5101_);
v___x_5141_ = lean_unbox_float(v_fst_5128_);
lean_dec(v_fst_5128_);
lean_ctor_set_float(v_data_5140_, sizeof(void*)*3, v___x_5141_);
v___x_5142_ = lean_unbox_float(v_snd_5129_);
lean_dec(v_snd_5129_);
lean_ctor_set_float(v_data_5140_, sizeof(void*)*3 + 8, v___x_5142_);
lean_ctor_set_uint8(v_data_5140_, sizeof(void*)*3 + 16, v_collapsed_5100_);
v___y_5115_ = v___y_5133_;
v___y_5116_ = v_a_5134_;
v_data_5117_ = v_data_5140_;
goto v___jp_5114_;
}
}
v___jp_5143_:
{
lean_object* v_ref_5144_; lean_object* v___x_5145_; 
v_ref_5144_ = lean_ctor_get(v___y_5109_, 2);
lean_inc(v___y_5110_);
lean_inc_ref(v___y_5109_);
lean_inc(v___y_5108_);
lean_inc_ref(v___y_5107_);
lean_inc(v_fst_5112_);
v___x_5145_ = lean_apply_6(v_msg_5105_, v_fst_5112_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, lean_box(0));
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v___x_5145_, 1);
v___y_5133_ = v_ref_5144_;
v_a_5134_ = v_a_5146_;
goto v___jp_5132_;
}
else
{
lean_object* v___x_5147_; 
lean_dec_ref_known(v___x_5145_, 1);
v___x_5147_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5133_ = v_ref_5144_;
v_a_5134_ = v___x_5147_;
goto v___jp_5132_;
}
}
v___jp_5148_:
{
if (v_clsEnabled_5103_ == 0)
{
if (v___y_5149_ == 0)
{
lean_object* v___x_5150_; lean_object* v_traceState_5151_; lean_object* v_env_5152_; lean_object* v_nextMacroScope_5153_; lean_object* v_ngen_5154_; lean_object* v_auxDeclNGen_5155_; lean_object* v_cache_5156_; lean_object* v_messages_5157_; lean_object* v_infoState_5158_; lean_object* v_snapshotTasks_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5178_; 
lean_dec(v_snd_5129_);
lean_dec(v_fst_5128_);
lean_dec_ref(v_msg_5105_);
lean_dec_ref(v_tag_5101_);
lean_dec(v_cls_5099_);
v___x_5150_ = lean_st_ref_take(v___y_5110_);
v_traceState_5151_ = lean_ctor_get(v___x_5150_, 4);
v_env_5152_ = lean_ctor_get(v___x_5150_, 0);
v_nextMacroScope_5153_ = lean_ctor_get(v___x_5150_, 1);
v_ngen_5154_ = lean_ctor_get(v___x_5150_, 2);
v_auxDeclNGen_5155_ = lean_ctor_get(v___x_5150_, 3);
v_cache_5156_ = lean_ctor_get(v___x_5150_, 5);
v_messages_5157_ = lean_ctor_get(v___x_5150_, 6);
v_infoState_5158_ = lean_ctor_get(v___x_5150_, 7);
v_snapshotTasks_5159_ = lean_ctor_get(v___x_5150_, 8);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5161_ = v___x_5150_;
v_isShared_5162_ = v_isSharedCheck_5178_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_snapshotTasks_5159_);
lean_inc(v_infoState_5158_);
lean_inc(v_messages_5157_);
lean_inc(v_cache_5156_);
lean_inc(v_traceState_5151_);
lean_inc(v_auxDeclNGen_5155_);
lean_inc(v_ngen_5154_);
lean_inc(v_nextMacroScope_5153_);
lean_inc(v_env_5152_);
lean_dec(v___x_5150_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5178_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
uint64_t v_tid_5163_; lean_object* v_traces_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5177_; 
v_tid_5163_ = lean_ctor_get_uint64(v_traceState_5151_, sizeof(void*)*1);
v_traces_5164_ = lean_ctor_get(v_traceState_5151_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_traceState_5151_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5166_ = v_traceState_5151_;
v_isShared_5167_ = v_isSharedCheck_5177_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_traces_5164_);
lean_dec(v_traceState_5151_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5177_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5168_; lean_object* v___x_5170_; 
v___x_5168_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5104_, v_traces_5164_);
lean_dec_ref(v_traces_5164_);
if (v_isShared_5167_ == 0)
{
lean_ctor_set(v___x_5166_, 0, v___x_5168_);
v___x_5170_ = v___x_5166_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5168_);
lean_ctor_set_uint64(v_reuseFailAlloc_5176_, sizeof(void*)*1, v_tid_5163_);
v___x_5170_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5172_; 
if (v_isShared_5162_ == 0)
{
lean_ctor_set(v___x_5161_, 4, v___x_5170_);
v___x_5172_ = v___x_5161_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_env_5152_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_nextMacroScope_5153_);
lean_ctor_set(v_reuseFailAlloc_5175_, 2, v_ngen_5154_);
lean_ctor_set(v_reuseFailAlloc_5175_, 3, v_auxDeclNGen_5155_);
lean_ctor_set(v_reuseFailAlloc_5175_, 4, v___x_5170_);
lean_ctor_set(v_reuseFailAlloc_5175_, 5, v_cache_5156_);
lean_ctor_set(v_reuseFailAlloc_5175_, 6, v_messages_5157_);
lean_ctor_set(v_reuseFailAlloc_5175_, 7, v_infoState_5158_);
lean_ctor_set(v_reuseFailAlloc_5175_, 8, v_snapshotTasks_5159_);
v___x_5172_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
lean_object* v___x_5173_; lean_object* v___x_5174_; 
v___x_5173_ = lean_st_ref_put(v___y_5110_, v___x_5172_);
v___x_5174_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5112_);
return v___x_5174_;
}
}
}
}
}
else
{
goto v___jp_5143_;
}
}
else
{
goto v___jp_5143_;
}
}
v___jp_5179_:
{
double v___x_5181_; double v___x_5182_; double v___x_5183_; uint8_t v___x_5184_; 
v___x_5181_ = lean_unbox_float(v_snd_5129_);
v___x_5182_ = lean_unbox_float(v_fst_5128_);
v___x_5183_ = lean_float_sub(v___x_5181_, v___x_5182_);
v___x_5184_ = lean_float_decLt(v___y_5180_, v___x_5183_);
v___y_5149_ = v___x_5184_;
goto v___jp_5148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5195_, lean_object* v_collapsed_5196_, lean_object* v_tag_5197_, lean_object* v_opts_5198_, lean_object* v_clsEnabled_5199_, lean_object* v_oldTraces_5200_, lean_object* v_msg_5201_, lean_object* v_resStartStop_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
uint8_t v_collapsed_boxed_5208_; uint8_t v_clsEnabled_boxed_5209_; lean_object* v_res_5210_; 
v_collapsed_boxed_5208_ = lean_unbox(v_collapsed_5196_);
v_clsEnabled_boxed_5209_ = lean_unbox(v_clsEnabled_5199_);
v_res_5210_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5195_, v_collapsed_boxed_5208_, v_tag_5197_, v_opts_5198_, v_clsEnabled_boxed_5209_, v_oldTraces_5200_, v_msg_5201_, v_resStartStop_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec_ref(v_opts_5198_);
return v_res_5210_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
v_cls_5215_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5216_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5217_ = l_Lean_Name_append(v___x_5216_, v_cls_5215_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_){
_start:
{
lean_object* v___y_5225_; lean_object* v_toCold_5243_; lean_object* v_options_5244_; lean_object* v_inheritedTraceOptions_5245_; uint8_t v_hasTrace_5246_; lean_object* v_cls_5247_; uint8_t v___x_5248_; 
v_toCold_5243_ = lean_ctor_get(v_a_5221_, 0);
v_options_5244_ = lean_ctor_get(v_toCold_5243_, 2);
v_inheritedTraceOptions_5245_ = lean_ctor_get(v_toCold_5243_, 11);
v_hasTrace_5246_ = lean_ctor_get_uint8(v_options_5244_, sizeof(void*)*1);
v_cls_5247_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5248_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5218_);
if (v_hasTrace_5246_ == 0)
{
lean_object* v___x_5249_; 
v___x_5249_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5248_, v_e_5218_, v_cls_5247_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
v___y_5225_ = v___x_5249_;
goto v___jp_5224_;
}
else
{
lean_object* v___f_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; uint8_t v___x_5253_; lean_object* v___y_5255_; lean_object* v___y_5256_; lean_object* v_a_5257_; lean_object* v___y_5270_; lean_object* v___y_5271_; lean_object* v_a_5272_; 
v___f_5250_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5251_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5252_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5245_, v_options_5244_, v___x_5252_);
if (v___x_5253_ == 0)
{
lean_object* v___x_5322_; uint8_t v___x_5323_; 
v___x_5322_ = l_Lean_trace_profiler;
v___x_5323_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5244_, v___x_5322_);
if (v___x_5323_ == 0)
{
lean_object* v___x_5324_; 
v___x_5324_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5248_, v_e_5218_, v_cls_5247_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
v___y_5225_ = v___x_5324_;
goto v___jp_5224_;
}
else
{
goto v___jp_5281_;
}
}
else
{
goto v___jp_5281_;
}
v___jp_5254_:
{
lean_object* v___x_5258_; double v___x_5259_; double v___x_5260_; double v___x_5261_; double v___x_5262_; double v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5258_ = lean_io_mono_nanos_now();
v___x_5259_ = lean_float_of_nat(v___y_5255_);
v___x_5260_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5261_ = lean_float_div(v___x_5259_, v___x_5260_);
v___x_5262_ = lean_float_of_nat(v___x_5258_);
v___x_5263_ = lean_float_div(v___x_5262_, v___x_5260_);
v___x_5264_ = lean_box_float(v___x_5261_);
v___x_5265_ = lean_box_float(v___x_5263_);
v___x_5266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5264_);
lean_ctor_set(v___x_5266_, 1, v___x_5265_);
v___x_5267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5267_, 0, v_a_5257_);
lean_ctor_set(v___x_5267_, 1, v___x_5266_);
v___x_5268_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5247_, v_hasTrace_5246_, v___x_5251_, v_options_5244_, v___x_5253_, v___y_5256_, v___f_5250_, v___x_5267_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
v___y_5225_ = v___x_5268_;
goto v___jp_5224_;
}
v___jp_5269_:
{
lean_object* v___x_5273_; double v___x_5274_; double v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v___x_5273_ = lean_io_get_num_heartbeats();
v___x_5274_ = lean_float_of_nat(v___y_5271_);
v___x_5275_ = lean_float_of_nat(v___x_5273_);
v___x_5276_ = lean_box_float(v___x_5274_);
v___x_5277_ = lean_box_float(v___x_5275_);
v___x_5278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5276_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
v___x_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5279_, 0, v_a_5272_);
lean_ctor_set(v___x_5279_, 1, v___x_5278_);
v___x_5280_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5247_, v_hasTrace_5246_, v___x_5251_, v_options_5244_, v___x_5253_, v___y_5270_, v___f_5250_, v___x_5279_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
v___y_5225_ = v___x_5280_;
goto v___jp_5224_;
}
v___jp_5281_:
{
lean_object* v___x_5282_; lean_object* v_a_5283_; lean_object* v___x_5284_; uint8_t v___x_5285_; 
v___x_5282_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5222_);
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
lean_inc(v_a_5283_);
lean_dec_ref(v___x_5282_);
v___x_5284_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5285_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5244_, v___x_5284_);
if (v___x_5285_ == 0)
{
lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5286_ = lean_io_mono_nanos_now();
v___x_5287_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5248_, v_e_5218_, v_cls_5247_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5295_; 
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___x_5287_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
lean_ctor_set_tag(v___x_5290_, 1);
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
v___y_5255_ = v___x_5286_;
v___y_5256_ = v_a_5283_;
v_a_5257_ = v___x_5293_;
goto v___jp_5254_;
}
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
v_a_5296_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5287_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5287_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
lean_ctor_set_tag(v___x_5298_, 0);
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
v___y_5255_ = v___x_5286_;
v___y_5256_ = v_a_5283_;
v_a_5257_ = v___x_5301_;
goto v___jp_5254_;
}
}
}
}
else
{
lean_object* v___x_5304_; lean_object* v___x_5305_; 
v___x_5304_ = lean_io_get_num_heartbeats();
v___x_5305_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5248_, v_e_5218_, v_cls_5247_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5305_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5305_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
lean_ctor_set_tag(v___x_5308_, 1);
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
v___y_5270_ = v_a_5283_;
v___y_5271_ = v___x_5304_;
v_a_5272_ = v___x_5311_;
goto v___jp_5269_;
}
}
}
else
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5321_; 
v_a_5314_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5316_ = v___x_5305_;
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5305_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5319_; 
if (v_isShared_5317_ == 0)
{
lean_ctor_set_tag(v___x_5316_, 0);
v___x_5319_ = v___x_5316_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5314_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
v___y_5270_ = v_a_5283_;
v___y_5271_ = v___x_5304_;
v_a_5272_ = v___x_5319_;
goto v___jp_5269_;
}
}
}
}
}
}
v___jp_5224_:
{
if (lean_obj_tag(v___y_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5234_; 
v_a_5226_ = lean_ctor_get(v___y_5225_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___y_5225_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5228_ = v___y_5225_;
v_isShared_5229_ = v_isSharedCheck_5234_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___y_5225_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5234_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v_fst_5230_; lean_object* v___x_5232_; 
v_fst_5230_ = lean_ctor_get(v_a_5226_, 0);
lean_inc(v_fst_5230_);
lean_dec(v_a_5226_);
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 0, v_fst_5230_);
v___x_5232_ = v___x_5228_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_fst_5230_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
v_a_5235_ = lean_ctor_get(v___y_5225_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___y_5225_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___y_5225_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___y_5225_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_);
lean_dec(v_a_5329_);
lean_dec_ref(v_a_5328_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5332_, lean_object* v_x_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v___x_5339_; 
v___x_5339_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5333_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5340_, lean_object* v_x_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5340_, v_x_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5348_, lean_object* v___y_5349_){
_start:
{
uint8_t v___x_5351_; 
v___x_5351_ = l_Lean_Expr_hasMVar(v_e_5348_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; 
v___x_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5352_, 0, v_e_5348_);
return v___x_5352_;
}
else
{
lean_object* v___x_5353_; lean_object* v_mctx_5354_; lean_object* v___x_5355_; lean_object* v_fst_5356_; lean_object* v_snd_5357_; lean_object* v___x_5358_; lean_object* v_cache_5359_; lean_object* v_zetaDeltaFVarIds_5360_; lean_object* v_postponed_5361_; lean_object* v_diag_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5371_; 
v___x_5353_ = lean_st_ref_get(v___y_5349_);
v_mctx_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc_ref(v_mctx_5354_);
lean_dec(v___x_5353_);
v___x_5355_ = l_Lean_instantiateMVarsCore(v_mctx_5354_, v_e_5348_);
v_fst_5356_ = lean_ctor_get(v___x_5355_, 0);
lean_inc(v_fst_5356_);
v_snd_5357_ = lean_ctor_get(v___x_5355_, 1);
lean_inc(v_snd_5357_);
lean_dec_ref(v___x_5355_);
v___x_5358_ = lean_st_ref_take(v___y_5349_);
v_cache_5359_ = lean_ctor_get(v___x_5358_, 1);
v_zetaDeltaFVarIds_5360_ = lean_ctor_get(v___x_5358_, 2);
v_postponed_5361_ = lean_ctor_get(v___x_5358_, 3);
v_diag_5362_ = lean_ctor_get(v___x_5358_, 4);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v___x_5358_, 0);
lean_dec(v_unused_5372_);
v___x_5364_ = v___x_5358_;
v_isShared_5365_ = v_isSharedCheck_5371_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_diag_5362_);
lean_inc(v_postponed_5361_);
lean_inc(v_zetaDeltaFVarIds_5360_);
lean_inc(v_cache_5359_);
lean_dec(v___x_5358_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5371_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 0, v_snd_5357_);
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_snd_5357_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v_cache_5359_);
lean_ctor_set(v_reuseFailAlloc_5370_, 2, v_zetaDeltaFVarIds_5360_);
lean_ctor_set(v_reuseFailAlloc_5370_, 3, v_postponed_5361_);
lean_ctor_set(v_reuseFailAlloc_5370_, 4, v_diag_5362_);
v___x_5367_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5368_ = lean_st_ref_put(v___y_5349_, v___x_5367_);
v___x_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5369_, 0, v_fst_5356_);
return v___x_5369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5373_, v___y_5374_);
lean_dec(v___y_5374_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_){
_start:
{
lean_object* v___x_5383_; 
v___x_5383_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5377_, v___y_5379_);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5391_, lean_object* v_opts_5392_, lean_object* v_act_5393_, lean_object* v_decl_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; 
lean_inc(v___y_5398_);
lean_inc_ref(v___y_5397_);
lean_inc(v___y_5396_);
lean_inc_ref(v___y_5395_);
v___x_5400_ = lean_apply_4(v_act_5393_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
v___x_5401_ = l_Lean_profileitIOUnsafe___redArg(v_category_5391_, v_opts_5392_, v___x_5400_, v_decl_5394_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5402_, lean_object* v_opts_5403_, lean_object* v_act_5404_, lean_object* v_decl_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5402_, v_opts_5403_, v_act_5404_, v_decl_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5406_);
lean_dec_ref(v_opts_5403_);
lean_dec_ref(v_category_5402_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5412_, lean_object* v_category_5413_, lean_object* v_opts_5414_, lean_object* v_act_5415_, lean_object* v_decl_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_){
_start:
{
lean_object* v___x_5422_; 
v___x_5422_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5413_, v_opts_5414_, v_act_5415_, v_decl_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
return v___x_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5423_, lean_object* v_category_5424_, lean_object* v_opts_5425_, lean_object* v_act_5426_, lean_object* v_decl_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_){
_start:
{
lean_object* v_res_5433_; 
v_res_5433_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5423_, v_category_5424_, v_opts_5425_, v_act_5426_, v_decl_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec_ref(v_opts_5425_);
lean_dec_ref(v_category_5424_);
return v_res_5433_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5434_, uint8_t v_isExporting_5435_, lean_object* v___x_5436_, lean_object* v___y_5437_, lean_object* v___x_5438_, lean_object* v_a_x3f_5439_){
_start:
{
lean_object* v___x_5441_; lean_object* v_env_5442_; lean_object* v_nextMacroScope_5443_; lean_object* v_ngen_5444_; lean_object* v_auxDeclNGen_5445_; lean_object* v_traceState_5446_; lean_object* v_messages_5447_; lean_object* v_infoState_5448_; lean_object* v_snapshotTasks_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5474_; 
v___x_5441_ = lean_st_ref_take(v___y_5434_);
v_env_5442_ = lean_ctor_get(v___x_5441_, 0);
v_nextMacroScope_5443_ = lean_ctor_get(v___x_5441_, 1);
v_ngen_5444_ = lean_ctor_get(v___x_5441_, 2);
v_auxDeclNGen_5445_ = lean_ctor_get(v___x_5441_, 3);
v_traceState_5446_ = lean_ctor_get(v___x_5441_, 4);
v_messages_5447_ = lean_ctor_get(v___x_5441_, 6);
v_infoState_5448_ = lean_ctor_get(v___x_5441_, 7);
v_snapshotTasks_5449_ = lean_ctor_get(v___x_5441_, 8);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5474_ == 0)
{
lean_object* v_unused_5475_; 
v_unused_5475_ = lean_ctor_get(v___x_5441_, 5);
lean_dec(v_unused_5475_);
v___x_5451_ = v___x_5441_;
v_isShared_5452_ = v_isSharedCheck_5474_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_snapshotTasks_5449_);
lean_inc(v_infoState_5448_);
lean_inc(v_messages_5447_);
lean_inc(v_traceState_5446_);
lean_inc(v_auxDeclNGen_5445_);
lean_inc(v_ngen_5444_);
lean_inc(v_nextMacroScope_5443_);
lean_inc(v_env_5442_);
lean_dec(v___x_5441_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5474_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5453_; lean_object* v___x_5455_; 
v___x_5453_ = l_Lean_Environment_setExporting(v_env_5442_, v_isExporting_5435_);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 5, v___x_5436_);
lean_ctor_set(v___x_5451_, 0, v___x_5453_);
v___x_5455_ = v___x_5451_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5453_);
lean_ctor_set(v_reuseFailAlloc_5473_, 1, v_nextMacroScope_5443_);
lean_ctor_set(v_reuseFailAlloc_5473_, 2, v_ngen_5444_);
lean_ctor_set(v_reuseFailAlloc_5473_, 3, v_auxDeclNGen_5445_);
lean_ctor_set(v_reuseFailAlloc_5473_, 4, v_traceState_5446_);
lean_ctor_set(v_reuseFailAlloc_5473_, 5, v___x_5436_);
lean_ctor_set(v_reuseFailAlloc_5473_, 6, v_messages_5447_);
lean_ctor_set(v_reuseFailAlloc_5473_, 7, v_infoState_5448_);
lean_ctor_set(v_reuseFailAlloc_5473_, 8, v_snapshotTasks_5449_);
v___x_5455_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v_mctx_5458_; lean_object* v_zetaDeltaFVarIds_5459_; lean_object* v_postponed_5460_; lean_object* v_diag_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5471_; 
v___x_5456_ = lean_st_ref_put(v___y_5434_, v___x_5455_);
v___x_5457_ = lean_st_ref_take(v___y_5437_);
v_mctx_5458_ = lean_ctor_get(v___x_5457_, 0);
v_zetaDeltaFVarIds_5459_ = lean_ctor_get(v___x_5457_, 2);
v_postponed_5460_ = lean_ctor_get(v___x_5457_, 3);
v_diag_5461_ = lean_ctor_get(v___x_5457_, 4);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5457_);
if (v_isSharedCheck_5471_ == 0)
{
lean_object* v_unused_5472_; 
v_unused_5472_ = lean_ctor_get(v___x_5457_, 1);
lean_dec(v_unused_5472_);
v___x_5463_ = v___x_5457_;
v_isShared_5464_ = v_isSharedCheck_5471_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_diag_5461_);
lean_inc(v_postponed_5460_);
lean_inc(v_zetaDeltaFVarIds_5459_);
lean_inc(v_mctx_5458_);
lean_dec(v___x_5457_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5471_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5466_; 
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 1, v___x_5438_);
v___x_5466_ = v___x_5463_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_mctx_5458_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5470_, 2, v_zetaDeltaFVarIds_5459_);
lean_ctor_set(v_reuseFailAlloc_5470_, 3, v_postponed_5460_);
lean_ctor_set(v_reuseFailAlloc_5470_, 4, v_diag_5461_);
v___x_5466_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5467_ = lean_st_ref_put(v___y_5437_, v___x_5466_);
v___x_5468_ = lean_box(0);
v___x_5469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5469_, 0, v___x_5468_);
return v___x_5469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5476_, lean_object* v_isExporting_5477_, lean_object* v___x_5478_, lean_object* v___y_5479_, lean_object* v___x_5480_, lean_object* v_a_x3f_5481_, lean_object* v___y_5482_){
_start:
{
uint8_t v_isExporting_boxed_5483_; lean_object* v_res_5484_; 
v_isExporting_boxed_5483_ = lean_unbox(v_isExporting_5477_);
v_res_5484_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5476_, v_isExporting_boxed_5483_, v___x_5478_, v___y_5479_, v___x_5480_, v_a_x3f_5481_);
lean_dec(v_a_x3f_5481_);
lean_dec(v___y_5479_);
lean_dec(v___y_5476_);
return v_res_5484_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5485_; 
v___x_5485_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5485_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5486_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5487_, 0, v___x_5486_);
return v___x_5487_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5488_; lean_object* v___x_5489_; 
v___x_5488_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5488_);
lean_ctor_set(v___x_5489_, 1, v___x_5488_);
return v___x_5489_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5490_; lean_object* v___x_5491_; 
v___x_5490_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5491_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5491_, 0, v___x_5490_);
lean_ctor_set(v___x_5491_, 1, v___x_5490_);
lean_ctor_set(v___x_5491_, 2, v___x_5490_);
lean_ctor_set(v___x_5491_, 3, v___x_5490_);
lean_ctor_set(v___x_5491_, 4, v___x_5490_);
lean_ctor_set(v___x_5491_, 5, v___x_5490_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5492_, uint8_t v_isExporting_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_){
_start:
{
lean_object* v___x_5499_; lean_object* v_env_5500_; lean_object* v___x_5501_; uint8_t v_isModule_5502_; 
v___x_5499_ = lean_st_ref_get(v___y_5497_);
v_env_5500_ = lean_ctor_get(v___x_5499_, 0);
lean_inc_ref(v_env_5500_);
lean_dec(v___x_5499_);
v___x_5501_ = l_Lean_Environment_header(v_env_5500_);
v_isModule_5502_ = lean_ctor_get_uint8(v___x_5501_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5501_);
if (v_isModule_5502_ == 0)
{
lean_object* v___x_5503_; 
lean_dec_ref(v_env_5500_);
lean_inc(v___y_5497_);
lean_inc_ref(v___y_5496_);
lean_inc(v___y_5495_);
lean_inc_ref(v___y_5494_);
v___x_5503_ = lean_apply_5(v_x_5492_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, lean_box(0));
return v___x_5503_;
}
else
{
uint8_t v_isExporting_5504_; 
v_isExporting_5504_ = lean_ctor_get_uint8(v_env_5500_, sizeof(void*)*8);
lean_dec_ref(v_env_5500_);
if (v_isExporting_5493_ == 0)
{
if (v_isExporting_5504_ == 0)
{
lean_object* v___x_5570_; 
lean_inc(v___y_5497_);
lean_inc_ref(v___y_5496_);
lean_inc(v___y_5495_);
lean_inc_ref(v___y_5494_);
v___x_5570_ = lean_apply_5(v_x_5492_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, lean_box(0));
return v___x_5570_;
}
else
{
goto v___jp_5505_;
}
}
else
{
if (v_isExporting_5504_ == 0)
{
goto v___jp_5505_;
}
else
{
lean_object* v___x_5571_; 
lean_inc(v___y_5497_);
lean_inc_ref(v___y_5496_);
lean_inc(v___y_5495_);
lean_inc_ref(v___y_5494_);
v___x_5571_ = lean_apply_5(v_x_5492_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, lean_box(0));
return v___x_5571_;
}
}
v___jp_5505_:
{
lean_object* v___x_5506_; lean_object* v_env_5507_; lean_object* v_nextMacroScope_5508_; lean_object* v_ngen_5509_; lean_object* v_auxDeclNGen_5510_; lean_object* v_traceState_5511_; lean_object* v_messages_5512_; lean_object* v_infoState_5513_; lean_object* v_snapshotTasks_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5568_; 
v___x_5506_ = lean_st_ref_take(v___y_5497_);
v_env_5507_ = lean_ctor_get(v___x_5506_, 0);
v_nextMacroScope_5508_ = lean_ctor_get(v___x_5506_, 1);
v_ngen_5509_ = lean_ctor_get(v___x_5506_, 2);
v_auxDeclNGen_5510_ = lean_ctor_get(v___x_5506_, 3);
v_traceState_5511_ = lean_ctor_get(v___x_5506_, 4);
v_messages_5512_ = lean_ctor_get(v___x_5506_, 6);
v_infoState_5513_ = lean_ctor_get(v___x_5506_, 7);
v_snapshotTasks_5514_ = lean_ctor_get(v___x_5506_, 8);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5568_ == 0)
{
lean_object* v_unused_5569_; 
v_unused_5569_ = lean_ctor_get(v___x_5506_, 5);
lean_dec(v_unused_5569_);
v___x_5516_ = v___x_5506_;
v_isShared_5517_ = v_isSharedCheck_5568_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_snapshotTasks_5514_);
lean_inc(v_infoState_5513_);
lean_inc(v_messages_5512_);
lean_inc(v_traceState_5511_);
lean_inc(v_auxDeclNGen_5510_);
lean_inc(v_ngen_5509_);
lean_inc(v_nextMacroScope_5508_);
lean_inc(v_env_5507_);
lean_dec(v___x_5506_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5568_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5521_; 
v___x_5518_ = l_Lean_Environment_setExporting(v_env_5507_, v_isExporting_5493_);
v___x_5519_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 5, v___x_5519_);
lean_ctor_set(v___x_5516_, 0, v___x_5518_);
v___x_5521_ = v___x_5516_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5518_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v_nextMacroScope_5508_);
lean_ctor_set(v_reuseFailAlloc_5567_, 2, v_ngen_5509_);
lean_ctor_set(v_reuseFailAlloc_5567_, 3, v_auxDeclNGen_5510_);
lean_ctor_set(v_reuseFailAlloc_5567_, 4, v_traceState_5511_);
lean_ctor_set(v_reuseFailAlloc_5567_, 5, v___x_5519_);
lean_ctor_set(v_reuseFailAlloc_5567_, 6, v_messages_5512_);
lean_ctor_set(v_reuseFailAlloc_5567_, 7, v_infoState_5513_);
lean_ctor_set(v_reuseFailAlloc_5567_, 8, v_snapshotTasks_5514_);
v___x_5521_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v_mctx_5524_; lean_object* v_zetaDeltaFVarIds_5525_; lean_object* v_postponed_5526_; lean_object* v_diag_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5565_; 
v___x_5522_ = lean_st_ref_put(v___y_5497_, v___x_5521_);
v___x_5523_ = lean_st_ref_take(v___y_5495_);
v_mctx_5524_ = lean_ctor_get(v___x_5523_, 0);
v_zetaDeltaFVarIds_5525_ = lean_ctor_get(v___x_5523_, 2);
v_postponed_5526_ = lean_ctor_get(v___x_5523_, 3);
v_diag_5527_ = lean_ctor_get(v___x_5523_, 4);
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5565_ == 0)
{
lean_object* v_unused_5566_; 
v_unused_5566_ = lean_ctor_get(v___x_5523_, 1);
lean_dec(v_unused_5566_);
v___x_5529_ = v___x_5523_;
v_isShared_5530_ = v_isSharedCheck_5565_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_diag_5527_);
lean_inc(v_postponed_5526_);
lean_inc(v_zetaDeltaFVarIds_5525_);
lean_inc(v_mctx_5524_);
lean_dec(v___x_5523_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5565_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5531_; lean_object* v___x_5533_; 
v___x_5531_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5530_ == 0)
{
lean_ctor_set(v___x_5529_, 1, v___x_5531_);
v___x_5533_ = v___x_5529_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_mctx_5524_);
lean_ctor_set(v_reuseFailAlloc_5564_, 1, v___x_5531_);
lean_ctor_set(v_reuseFailAlloc_5564_, 2, v_zetaDeltaFVarIds_5525_);
lean_ctor_set(v_reuseFailAlloc_5564_, 3, v_postponed_5526_);
lean_ctor_set(v_reuseFailAlloc_5564_, 4, v_diag_5527_);
v___x_5533_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
lean_object* v___x_5534_; lean_object* v_r_5535_; 
v___x_5534_ = lean_st_ref_put(v___y_5495_, v___x_5533_);
lean_inc(v___y_5497_);
lean_inc_ref(v___y_5496_);
lean_inc(v___y_5495_);
lean_inc_ref(v___y_5494_);
v_r_5535_ = lean_apply_5(v_x_5492_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, lean_box(0));
if (lean_obj_tag(v_r_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5552_; 
v_a_5536_ = lean_ctor_get(v_r_5535_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_r_5535_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5538_ = v_r_5535_;
v_isShared_5539_ = v_isSharedCheck_5552_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v_r_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5552_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
lean_inc(v_a_5536_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set_tag(v___x_5538_, 1);
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5536_);
v___x_5541_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
v___x_5542_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5497_, v_isExporting_5504_, v___x_5519_, v___y_5495_, v___x_5531_, v___x_5541_);
lean_dec_ref(v___x_5541_);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; 
v_unused_5550_ = lean_ctor_get(v___x_5542_, 0);
lean_dec(v_unused_5550_);
v___x_5544_ = v___x_5542_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_dec(v___x_5542_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
lean_ctor_set(v___x_5544_, 0, v_a_5536_);
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5536_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
}
else
{
lean_object* v_a_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
v_a_5553_ = lean_ctor_get(v_r_5535_, 0);
lean_inc(v_a_5553_);
lean_dec_ref_known(v_r_5535_, 1);
v___x_5554_ = lean_box(0);
v___x_5555_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5497_, v_isExporting_5504_, v___x_5519_, v___y_5495_, v___x_5531_, v___x_5554_);
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
lean_ctor_set_tag(v___x_5557_, 1);
lean_ctor_set(v___x_5557_, 0, v_a_5553_);
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5553_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5572_, lean_object* v_isExporting_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_){
_start:
{
uint8_t v_isExporting_boxed_5579_; lean_object* v_res_5580_; 
v_isExporting_boxed_5579_ = lean_unbox(v_isExporting_5573_);
v_res_5580_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5572_, v_isExporting_boxed_5579_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
return v_res_5580_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5581_, uint8_t v_when_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_){
_start:
{
if (v_when_5582_ == 0)
{
lean_object* v___x_5588_; 
lean_inc(v___y_5586_);
lean_inc_ref(v___y_5585_);
lean_inc(v___y_5584_);
lean_inc_ref(v___y_5583_);
v___x_5588_ = lean_apply_5(v_x_5581_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, lean_box(0));
return v___x_5588_;
}
else
{
uint8_t v___x_5589_; lean_object* v___x_5590_; 
v___x_5589_ = 0;
v___x_5590_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5581_, v___x_5589_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
return v___x_5590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5591_, lean_object* v_when_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_){
_start:
{
uint8_t v_when_boxed_5598_; lean_object* v_res_5599_; 
v_when_boxed_5598_ = lean_unbox(v_when_5592_);
v_res_5599_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5591_, v_when_boxed_5598_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
lean_object* v___x_5606_; lean_object* v_a_5607_; lean_object* v___x_5608_; uint8_t v___x_5609_; lean_object* v___x_5610_; 
v___x_5606_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5600_, v___y_5602_);
v_a_5607_ = lean_ctor_get(v___x_5606_, 0);
lean_inc(v_a_5607_);
lean_dec_ref(v___x_5606_);
v___x_5608_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5608_, 0, v_a_5607_);
v___x_5609_ = 1;
v___x_5610_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5608_, v___x_5609_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
return v___x_5610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_){
_start:
{
lean_object* v_res_5617_; 
v_res_5617_ = l_Lean_Meta_letToHave___lam__0(v_e_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
return v_res_5617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_){
_start:
{
lean_object* v_toCold_5625_; lean_object* v_options_5626_; lean_object* v___f_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v_toCold_5625_ = lean_ctor_get(v_a_5622_, 0);
v_options_5626_ = lean_ctor_get(v_toCold_5625_, 2);
v___f_5627_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5627_, 0, v_e_5619_);
v___x_5628_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5629_ = lean_box(0);
v___x_5630_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5628_, v_options_5626_, v___f_5627_, v___x_5629_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_);
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_){
_start:
{
lean_object* v_res_5637_; 
v_res_5637_ = l_Lean_Meta_letToHave(v_e_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_);
lean_dec(v_a_5635_);
lean_dec_ref(v_a_5634_);
lean_dec(v_a_5633_);
lean_dec_ref(v_a_5632_);
return v_res_5637_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5638_, lean_object* v_x_5639_, uint8_t v_isExporting_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
lean_object* v___x_5646_; 
v___x_5646_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5639_, v_isExporting_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
return v___x_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5647_, lean_object* v_x_5648_, lean_object* v_isExporting_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_){
_start:
{
uint8_t v_isExporting_boxed_5655_; lean_object* v_res_5656_; 
v_isExporting_boxed_5655_ = lean_unbox(v_isExporting_5649_);
v_res_5656_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5647_, v_x_5648_, v_isExporting_boxed_5655_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec(v___y_5651_);
lean_dec_ref(v___y_5650_);
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5657_, lean_object* v_x_5658_, uint8_t v_when_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v___x_5665_; 
v___x_5665_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5658_, v_when_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5666_, lean_object* v_x_5667_, lean_object* v_when_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
uint8_t v_when_boxed_5674_; lean_object* v_res_5675_; 
v_when_boxed_5674_ = lean_unbox(v_when_5668_);
v_res_5675_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5666_, v_x_5667_, v_when_boxed_5674_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
return v_res_5675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5732_; uint8_t v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; 
v___x_5732_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5733_ = 0;
v___x_5734_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5735_ = l_Lean_registerTraceClass(v___x_5732_, v___x_5733_, v___x_5734_);
if (lean_obj_tag(v___x_5735_) == 0)
{
lean_object* v___x_5736_; lean_object* v___x_5737_; 
lean_dec_ref_known(v___x_5735_, 1);
v___x_5736_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5737_ = l_Lean_registerTraceClass(v___x_5736_, v___x_5733_, v___x_5734_);
return v___x_5737_;
}
else
{
return v___x_5735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5738_){
_start:
{
lean_object* v_res_5739_; 
v_res_5739_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5739_;
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
