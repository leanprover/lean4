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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addZetaDeltaFVarId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27;
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
uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0(lean_object* v_x_1_){
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
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint8_t v_res_6_;
v_res_6_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0(v_x_1_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0___boxed(lean_object* v_x_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0(v_x_7_);
lean_dec_ref(v_x_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(lean_object* v_e_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; 
v___f_12_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___closed__0));
v___x_13_ = lean_find_expr(v___f_12_, v_e_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
uint8_t v___x_14_; 
v___x_14_ = 0;
return v___x_14_;
}
else
{
uint8_t v___x_15_; 
lean_dec_ref_known(v___x_13_, 1);
v___x_15_ = 1;
return v___x_15_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_11_ = stack[0].m_obj;
uint8_t v_res_16_;
v_res_16_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_11_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___boxed(lean_object* v_e_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_17_);
lean_dec_ref(v_e_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(lean_object* v_e_20_, uint32_t v_maxDepth_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = l_Lean_Expr_hasFVar(v_e_20_);
if (v___x_22_ == 0)
{
uint8_t v___x_23_; 
v___x_23_ = l_Lean_Expr_hasExprMVar(v_e_20_);
if (v___x_23_ == 0)
{
uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = l_Lean_Expr_approxDepth(v_e_20_);
v___x_25_ = lean_uint32_dec_le(v___x_24_, v_maxDepth_21_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_20_);
if (v___x_26_ == 0)
{
return v___x_25_;
}
else
{
return v___x_23_;
}
}
}
else
{
return v___x_22_;
}
}
else
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_20_ = stack[0].m_obj;
uint32_t v_maxDepth_21_ = stack[1].m_num;
uint8_t v_res_28_;
v_res_28_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_20_, v_maxDepth_21_);
stack->m_num = v_res_28_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip___boxed(lean_object* v_e_29_, lean_object* v_maxDepth_30_){
_start:
{
uint32_t v_maxDepth_boxed_31_; uint8_t v_res_32_; lean_object* v_r_33_; 
v_maxDepth_boxed_31_ = lean_unbox_uint32(v_maxDepth_30_);
lean_dec(v_maxDepth_30_);
v_res_32_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_29_, v_maxDepth_boxed_31_);
lean_dec_ref(v_e_29_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
v___x_38_ = ((lean_object*)(l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__1));
v___x_39_ = l_Lean_Expr_const___override(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_box(0);
v___x_41_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0(lean_object* v_self_45_){
_start:
{
lean_object* v_expr_46_; 
v_expr_46_ = lean_ctor_get(v_self_45_, 0);
lean_inc_ref(v_expr_46_);
return v_expr_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0___boxed(lean_object* v_self_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0(v_self_47_);
lean_dec_ref(v_self_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(lean_object* v_a_51_, lean_object* v_b_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_dec(v_b_52_);
lean_dec_ref(v_a_51_);
return v_x_53_;
}
else
{
lean_object* v_key_54_; lean_object* v_value_55_; lean_object* v_tail_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_68_; 
v_key_54_ = lean_ctor_get(v_x_53_, 0);
v_value_55_ = lean_ctor_get(v_x_53_, 1);
v_tail_56_ = lean_ctor_get(v_x_53_, 2);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_68_ == 0)
{
v___x_58_ = v_x_53_;
v_isShared_59_ = v_isSharedCheck_68_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_tail_56_);
lean_inc(v_value_55_);
lean_inc(v_key_54_);
lean_dec(v_x_53_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_68_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
uint8_t v___x_60_; 
v___x_60_ = l_Lean_ExprStructEq_beq(v_key_54_, v_a_51_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_61_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_51_, v_b_52_, v_tail_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 2, v___x_61_);
v___x_63_ = v___x_58_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_key_54_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_value_55_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
else
{
lean_object* v___x_66_; 
lean_dec(v_value_55_);
lean_dec(v_key_54_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v_b_52_);
lean_ctor_set(v___x_58_, 0, v_a_51_);
v___x_66_ = v___x_58_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_51_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_b_52_);
lean_ctor_set(v_reuseFailAlloc_67_, 2, v_tail_56_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
return v_x_69_;
}
else
{
lean_object* v_key_71_; lean_object* v_value_72_; lean_object* v_tail_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_96_; 
v_key_71_ = lean_ctor_get(v_x_70_, 0);
v_value_72_ = lean_ctor_get(v_x_70_, 1);
v_tail_73_ = lean_ctor_get(v_x_70_, 2);
v_isSharedCheck_96_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_96_ == 0)
{
v___x_75_ = v_x_70_;
v_isShared_76_ = v_isSharedCheck_96_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_tail_73_);
lean_inc(v_value_72_);
lean_inc(v_key_71_);
lean_dec(v_x_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_96_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v_fold_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_77_ = lean_array_get_size(v_x_69_);
v___x_78_ = l_Lean_ExprStructEq_hash(v_key_71_);
v___x_79_ = 32ULL;
v___x_80_ = lean_uint64_shift_right(v___x_78_, v___x_79_);
v_fold_81_ = lean_uint64_xor(v___x_78_, v___x_80_);
v___x_82_ = 16ULL;
v___x_83_ = lean_uint64_shift_right(v_fold_81_, v___x_82_);
v___x_84_ = lean_uint64_xor(v_fold_81_, v___x_83_);
v___x_85_ = lean_uint64_to_usize(v___x_84_);
v___x_86_ = lean_usize_of_nat(v___x_77_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_sub(v___x_86_, v___x_87_);
v___x_89_ = lean_usize_land(v___x_85_, v___x_88_);
v___x_90_ = lean_array_uget_borrowed(v_x_69_, v___x_89_);
lean_inc(v___x_90_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 2, v___x_90_);
v___x_92_ = v___x_75_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_key_71_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_value_72_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v___x_90_);
v___x_92_ = v_reuseFailAlloc_95_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_array_uset(v_x_69_, v___x_89_, v___x_92_);
v_x_69_ = v___x_93_;
v_x_70_ = v_tail_73_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(lean_object* v_i_97_, lean_object* v_source_98_, lean_object* v_target_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_array_get_size(v_source_98_);
v___x_101_ = lean_nat_dec_lt(v_i_97_, v___x_100_);
if (v___x_101_ == 0)
{
lean_dec_ref(v_source_98_);
lean_dec(v_i_97_);
return v_target_99_;
}
else
{
lean_object* v_es_102_; lean_object* v___x_103_; lean_object* v_source_104_; lean_object* v_target_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_es_102_ = lean_array_fget(v_source_98_, v_i_97_);
v___x_103_ = lean_box(0);
v_source_104_ = lean_array_fset(v_source_98_, v_i_97_, v___x_103_);
v_target_105_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(v_target_99_, v_es_102_);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_i_97_, v___x_106_);
lean_dec(v_i_97_);
v_i_97_ = v___x_107_;
v_source_98_ = v_source_104_;
v_target_99_ = v_target_105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(lean_object* v_data_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_nbuckets_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_110_ = lean_array_get_size(v_data_109_);
v___x_111_ = lean_unsigned_to_nat(2u);
v_nbuckets_112_ = lean_nat_mul(v___x_110_, v___x_111_);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_box(0);
v___x_115_ = lean_mk_array(v_nbuckets_112_, v___x_114_);
v___x_116_ = lean_array_propagate_mark(v_data_109_, v___x_115_);
v___x_117_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v___x_113_, v_data_109_, v___x_116_);
return v___x_117_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(lean_object* v_a_118_, lean_object* v_x_119_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_118_ = stack[0].m_obj;
lean_object* v_x_119_ = stack[1].m_obj;
uint8_t v_res_125_;
v_res_125_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_118_, v_x_119_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg___boxed(lean_object* v_a_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec_ref(v_a_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(lean_object* v_m_130_, lean_object* v_a_131_, lean_object* v_b_132_){
_start:
{
lean_object* v_size_133_; lean_object* v_buckets_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_177_; 
v_size_133_ = lean_ctor_get(v_m_130_, 0);
v_buckets_134_ = lean_ctor_get(v_m_130_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_m_130_);
if (v_isSharedCheck_177_ == 0)
{
v___x_136_ = v_m_130_;
v_isShared_137_ = v_isSharedCheck_177_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_buckets_134_);
lean_inc(v_size_133_);
lean_dec(v_m_130_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_177_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v_fold_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v_bkt_151_; uint8_t v___x_152_; 
v___x_138_ = lean_array_get_size(v_buckets_134_);
v___x_139_ = l_Lean_ExprStructEq_hash(v_a_131_);
v___x_140_ = 32ULL;
v___x_141_ = lean_uint64_shift_right(v___x_139_, v___x_140_);
v_fold_142_ = lean_uint64_xor(v___x_139_, v___x_141_);
v___x_143_ = 16ULL;
v___x_144_ = lean_uint64_shift_right(v_fold_142_, v___x_143_);
v___x_145_ = lean_uint64_xor(v_fold_142_, v___x_144_);
v___x_146_ = lean_uint64_to_usize(v___x_145_);
v___x_147_ = lean_usize_of_nat(v___x_138_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_sub(v___x_147_, v___x_148_);
v___x_150_ = lean_usize_land(v___x_146_, v___x_149_);
v_bkt_151_ = lean_array_uget_borrowed(v_buckets_134_, v___x_150_);
v___x_152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_131_, v_bkt_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v_size_x27_154_; lean_object* v___x_155_; lean_object* v_buckets_x27_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v_size_x27_154_ = lean_nat_add(v_size_133_, v___x_153_);
lean_dec(v_size_133_);
lean_inc(v_bkt_151_);
v___x_155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_155_, 0, v_a_131_);
lean_ctor_set(v___x_155_, 1, v_b_132_);
lean_ctor_set(v___x_155_, 2, v_bkt_151_);
v_buckets_x27_156_ = lean_array_uset(v_buckets_134_, v___x_150_, v___x_155_);
v___x_157_ = lean_unsigned_to_nat(4u);
v___x_158_ = lean_nat_mul(v_size_x27_154_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(3u);
v___x_160_ = lean_nat_div(v___x_158_, v___x_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_array_get_size(v_buckets_x27_156_);
v___x_162_ = lean_nat_dec_le(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
if (v___x_162_ == 0)
{
lean_object* v_val_163_; lean_object* v___x_165_; 
v_val_163_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_buckets_x27_156_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v_val_163_);
lean_ctor_set(v___x_136_, 0, v_size_x27_154_);
v___x_165_ = v___x_136_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_size_x27_154_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_val_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
else
{
lean_object* v___x_168_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v_buckets_x27_156_);
lean_ctor_set(v___x_136_, 0, v_size_x27_154_);
v___x_168_ = v___x_136_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_size_x27_154_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_buckets_x27_156_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v___x_170_; lean_object* v_buckets_x27_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
lean_inc(v_bkt_151_);
v___x_170_ = lean_box(0);
v_buckets_x27_171_ = lean_array_uset(v_buckets_134_, v___x_150_, v___x_170_);
v___x_172_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_131_, v_b_132_, v_bkt_151_);
v___x_173_ = lean_array_uset(v_buckets_x27_171_, v___x_150_, v___x_172_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_173_);
v___x_175_ = v___x_136_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_size_133_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(lean_object* v_r_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_type_x3f_185_; 
v_type_x3f_185_ = lean_ctor_get(v_r_178_, 1);
lean_inc(v_type_x3f_185_);
if (lean_obj_tag(v_type_x3f_185_) == 1)
{
lean_object* v_val_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref(v_r_178_);
v_val_186_ = lean_ctor_get(v_type_x3f_185_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_type_x3f_185_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v_type_x3f_185_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_val_186_);
lean_dec(v_type_x3f_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 0);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_val_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_object* v_expr_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_type_x3f_185_);
v_expr_194_ = lean_ctor_get(v_r_178_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v_r_178_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v_r_178_, 1);
lean_dec(v_unused_224_);
v___x_196_ = v_r_178_;
v_isShared_197_ = v_isSharedCheck_223_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_expr_194_);
lean_dec(v_r_178_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_223_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; 
lean_inc(v_a_183_);
lean_inc_ref(v_a_182_);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc_ref(v_expr_194_);
v___x_198_ = lean_infer_type(v_expr_194_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_222_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_222_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_222_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_222_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_a_199_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_a_199_);
lean_inc_ref(v_expr_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_203_);
v___x_205_ = v___x_196_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_expr_194_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_221_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v_count_207_; lean_object* v_results_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_220_; 
v___x_206_ = lean_st_ref_take(v_a_179_);
v_count_207_ = lean_ctor_get(v___x_206_, 0);
v_results_208_ = lean_ctor_get(v___x_206_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_220_ == 0)
{
v___x_210_ = v___x_206_;
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_results_208_);
lean_inc(v_count_207_);
lean_dec(v___x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_208_, v_expr_194_, v___x_205_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_212_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_count_207_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_219_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_st_ref_put(v_a_179_, v___x_214_);
if (v_isShared_202_ == 0)
{
v___x_217_ = v___x_201_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_199_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_196_);
lean_dec_ref(v_expr_194_);
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_178_ = stack[0].m_obj;
lean_object* v_a_179_ = stack[1].m_obj;
lean_object* v_a_180_ = stack[2].m_obj;
lean_object* v_a_181_ = stack[3].m_obj;
lean_object* v_a_182_ = stack[4].m_obj;
lean_object* v_a_183_ = stack[5].m_obj;
lean_object* v_res_225_;
v_res_225_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg___boxed(lean_object* v_r_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
return v_res_233_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(lean_object* v_r_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_234_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
return v___x_242_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_234_ = stack[0].m_obj;
lean_object* v_a_235_ = stack[1].m_obj;
lean_object* v_a_236_ = stack[2].m_obj;
lean_object* v_a_237_ = stack[3].m_obj;
lean_object* v_a_238_ = stack[4].m_obj;
lean_object* v_a_239_ = stack[5].m_obj;
lean_object* v_a_240_ = stack[6].m_obj;
lean_object* v_res_243_;
v_res_243_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(v_r_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___boxed(lean_object* v_r_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(v_r_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec(v_a_245_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(lean_object* v_00_u03b2_253_, lean_object* v_m_254_, lean_object* v_a_255_, lean_object* v_b_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_m_254_, v_a_255_, v_b_256_);
return v___x_257_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_object* v_00_u03b2_258_, lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_259_, v_x_260_);
return v___x_261_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_259_ = stack[1].m_obj;
lean_object* v_x_260_ = stack[2].m_obj;
uint8_t v_res_262_;
v_res_262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_box(0), v_a_259_, v_x_260_);
stack->m_num = v_res_262_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___boxed(lean_object* v_00_u03b2_263_, lean_object* v_a_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(v_00_u03b2_263_, v_a_264_, v_x_265_);
lean_dec(v_x_265_);
lean_dec_ref(v_a_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1(lean_object* v_00_u03b2_268_, lean_object* v_data_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_data_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2(lean_object* v_00_u03b2_271_, lean_object* v_a_272_, lean_object* v_b_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_272_, v_b_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_276_, lean_object* v_i_277_, lean_object* v_source_278_, lean_object* v_target_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v_i_277_, v_source_278_, v_target_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(v_x_282_, v_x_283_);
return v___x_284_;
}
}
uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(lean_object* v_ctx_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_List_isEmpty___redArg(v_ctx_285_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
v___x_287_ = 1;
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_285_ = stack[0].m_obj;
uint8_t v_res_289_;
v_res_289_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_ctx_285_);
stack->m_num = v_res_289_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check___boxed(lean_object* v_ctx_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_ctx_290_);
lean_dec(v_ctx_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(lean_object* v_e_293_, lean_object* v_m_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_295_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_m_294_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_e_293_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
lean_dec_ref(v_e_293_);
lean_inc(v_a_300_);
lean_inc_ref(v_a_299_);
lean_inc(v_a_298_);
lean_inc_ref(v_a_297_);
lean_inc(v_a_296_);
lean_inc(v_a_295_);
v___x_306_ = lean_apply_7(v_m_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, lean_box(0));
return v___x_306_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_293_ = stack[0].m_obj;
lean_object* v_m_294_ = stack[1].m_obj;
lean_object* v_a_295_ = stack[2].m_obj;
lean_object* v_a_296_ = stack[3].m_obj;
lean_object* v_a_297_ = stack[4].m_obj;
lean_object* v_a_298_ = stack[5].m_obj;
lean_object* v_a_299_ = stack[6].m_obj;
lean_object* v_a_300_ = stack[7].m_obj;
lean_object* v_res_307_;
v_res_307_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_293_, v_m_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck___boxed(lean_object* v_e_308_, lean_object* v_m_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_308_, v_m_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec(v_a_310_);
return v_res_317_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(lean_object* v_fvars_318_, lean_object* v_m_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
v___x_326_ = lean_apply_7(v_m_319_, v_fvars_318_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
return v___x_326_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_318_ = stack[0].m_obj;
lean_object* v_m_319_ = stack[1].m_obj;
lean_object* v_a_320_ = stack[2].m_obj;
lean_object* v_a_321_ = stack[3].m_obj;
lean_object* v_a_322_ = stack[4].m_obj;
lean_object* v_a_323_ = stack[5].m_obj;
lean_object* v_a_324_ = stack[6].m_obj;
lean_object* v_res_327_;
v_res_327_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(v_fvars_318_, v_m_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg___boxed(lean_object* v_fvars_328_, lean_object* v_m_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(v_fvars_328_, v_m_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
return v_res_336_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(lean_object* v_00_u03b1_337_, lean_object* v_fvars_338_, lean_object* v_m_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; 
lean_inc(v_a_345_);
lean_inc_ref(v_a_344_);
lean_inc(v_a_343_);
lean_inc_ref(v_a_342_);
lean_inc(v_a_341_);
v___x_347_ = lean_apply_7(v_m_339_, v_fvars_338_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, lean_box(0));
return v___x_347_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_338_ = stack[1].m_obj;
lean_object* v_m_339_ = stack[2].m_obj;
lean_object* v_a_340_ = stack[3].m_obj;
lean_object* v_a_341_ = stack[4].m_obj;
lean_object* v_a_342_ = stack[5].m_obj;
lean_object* v_a_343_ = stack[6].m_obj;
lean_object* v_a_344_ = stack[7].m_obj;
lean_object* v_a_345_ = stack[8].m_obj;
lean_object* v_res_348_;
v_res_348_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(lean_box(0), v_fvars_338_, v_m_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed(lean_object* v_00_u03b1_349_, lean_object* v_fvars_350_, lean_object* v_m_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(v_00_u03b1_349_, v_fvars_350_, v_m_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec(v_a_352_);
return v_res_359_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v_count_363_; lean_object* v_results_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_376_; 
v___x_362_ = lean_st_ref_take(v_a_360_);
v_count_363_ = lean_ctor_get(v___x_362_, 0);
v_results_364_ = lean_ctor_get(v___x_362_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_376_ == 0)
{
v___x_366_ = v___x_362_;
v_isShared_367_ = v_isSharedCheck_376_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_results_364_);
lean_inc(v_count_363_);
lean_dec(v___x_362_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_376_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_368_ = lean_box(0);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_count_363_, v___x_369_);
lean_dec(v_count_363_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_370_);
v___x_372_ = v___x_366_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_results_364_);
v___x_372_ = v_reuseFailAlloc_375_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_st_ref_put(v_a_360_, v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_368_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_360_ = stack[0].m_obj;
lean_object* v_res_377_;
v_res_377_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_360_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg___boxed(lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_378_);
lean_dec(v_a_378_);
return v_res_380_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_382_);
return v___x_388_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_381_ = stack[0].m_obj;
lean_object* v_a_382_ = stack[1].m_obj;
lean_object* v_a_383_ = stack[2].m_obj;
lean_object* v_a_384_ = stack[3].m_obj;
lean_object* v_a_385_ = stack[4].m_obj;
lean_object* v_a_386_ = stack[5].m_obj;
lean_object* v_res_389_;
v_res_389_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___boxed(lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec(v_a_390_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(lean_object* v_a_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
return v___x_400_;
}
else
{
lean_object* v_key_401_; lean_object* v_value_402_; lean_object* v_tail_403_; uint8_t v___x_404_; 
v_key_401_ = lean_ctor_get(v_x_399_, 0);
v_value_402_ = lean_ctor_get(v_x_399_, 1);
v_tail_403_ = lean_ctor_get(v_x_399_, 2);
v___x_404_ = l_Lean_ExprStructEq_beq(v_key_401_, v_a_398_);
if (v___x_404_ == 0)
{
v_x_399_ = v_tail_403_;
goto _start;
}
else
{
lean_object* v___x_406_; 
lean_inc(v_value_402_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_value_402_);
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_407_, v_x_408_);
lean_dec(v_x_408_);
lean_dec_ref(v_a_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_buckets_412_; lean_object* v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v_fold_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_buckets_412_ = lean_ctor_get(v_m_410_, 1);
v___x_413_ = lean_array_get_size(v_buckets_412_);
v___x_414_ = l_Lean_ExprStructEq_hash(v_a_411_);
v___x_415_ = 32ULL;
v___x_416_ = lean_uint64_shift_right(v___x_414_, v___x_415_);
v_fold_417_ = lean_uint64_xor(v___x_414_, v___x_416_);
v___x_418_ = 16ULL;
v___x_419_ = lean_uint64_shift_right(v_fold_417_, v___x_418_);
v___x_420_ = lean_uint64_xor(v_fold_417_, v___x_419_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = lean_usize_of_nat(v___x_413_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_sub(v___x_422_, v___x_423_);
v___x_425_ = lean_usize_land(v___x_421_, v___x_424_);
v___x_426_ = lean_array_uget_borrowed(v_buckets_412_, v___x_425_);
v___x_427_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_411_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg___boxed(lean_object* v_m_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_428_, v_a_429_);
lean_dec_ref(v_a_429_);
lean_dec_ref(v_m_428_);
return v_res_430_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(lean_object* v_e_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; lean_object* v_results_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_st_ref_get(v_a_432_);
v_results_435_ = lean_ctor_get(v___x_434_, 1);
lean_inc_ref(v_results_435_);
lean_dec(v___x_434_);
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_results_435_, v_e_431_);
lean_dec_ref(v_results_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_431_ = stack[0].m_obj;
lean_object* v_a_432_ = stack[1].m_obj;
lean_object* v_res_438_;
v_res_438_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_431_, v_a_432_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg___boxed(lean_object* v_e_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_e_439_);
return v_res_442_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(lean_object* v_e_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_443_, v_a_445_);
return v___x_451_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_443_ = stack[0].m_obj;
lean_object* v_a_444_ = stack[1].m_obj;
lean_object* v_a_445_ = stack[2].m_obj;
lean_object* v_a_446_ = stack[3].m_obj;
lean_object* v_a_447_ = stack[4].m_obj;
lean_object* v_a_448_ = stack[5].m_obj;
lean_object* v_a_449_ = stack[6].m_obj;
lean_object* v_res_452_;
v_res_452_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(v_e_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___boxed(lean_object* v_e_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(v_e_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_e_453_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_m_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_463_, v_a_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___boxed(lean_object* v_00_u03b2_466_, lean_object* v_m_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(v_00_u03b2_466_, v_m_467_, v_a_468_);
lean_dec_ref(v_a_468_);
lean_dec_ref(v_m_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(lean_object* v_00_u03b2_470_, lean_object* v_a_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_474_, lean_object* v_a_475_, lean_object* v_x_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(v_00_u03b2_474_, v_a_475_, v_x_476_);
lean_dec(v_x_476_);
lean_dec_ref(v_a_475_);
return v_res_477_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(lean_object* v_e_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_r_488_; lean_object* v___y_489_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_518_; 
v___x_503_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_478_, v_a_481_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_518_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
v___jp_487_:
{
lean_object* v___x_490_; lean_object* v_count_491_; lean_object* v_results_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_502_; 
v___x_490_ = lean_st_ref_take(v___y_489_);
v_count_491_ = lean_ctor_get(v___x_490_, 0);
v_results_492_ = lean_ctor_get(v___x_490_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_502_ == 0)
{
v___x_494_ = v___x_490_;
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_results_492_);
lean_inc(v_count_491_);
lean_dec(v___x_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
lean_inc_ref(v_r_488_);
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_492_, v_e_478_, v_r_488_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_count_491_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_st_ref_put(v___y_489_, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v_r_488_);
return v___x_500_;
}
}
}
v_resetjp_505_:
{
if (lean_obj_tag(v_a_504_) == 1)
{
lean_object* v_val_508_; lean_object* v___x_510_; 
lean_dec_ref(v_m_479_);
lean_dec_ref(v_e_478_);
v_val_508_ = lean_ctor_get(v_a_504_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v_a_504_, 1);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v_val_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_val_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
uint32_t v___x_512_; uint8_t v___x_513_; 
lean_del_object(v___x_506_);
lean_dec(v_a_504_);
v___x_512_ = 2;
v___x_513_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_478_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_inc(v_a_485_);
lean_inc_ref(v_a_484_);
lean_inc(v_a_483_);
lean_inc_ref(v_a_482_);
lean_inc(v_a_481_);
lean_inc(v_a_480_);
v___x_514_ = lean_apply_7(v_m_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, lean_box(0));
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v_r_488_ = v_a_515_;
v___y_489_ = v_a_481_;
goto v___jp_487_;
}
else
{
lean_dec_ref(v_e_478_);
return v___x_514_;
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref(v_m_479_);
v___x_516_ = lean_box(0);
lean_inc_ref(v_e_478_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_e_478_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v_r_488_ = v___x_517_;
v___y_489_ = v_a_481_;
goto v___jp_487_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_478_ = stack[0].m_obj;
lean_object* v_m_479_ = stack[1].m_obj;
lean_object* v_a_480_ = stack[2].m_obj;
lean_object* v_a_481_ = stack[3].m_obj;
lean_object* v_a_482_ = stack[4].m_obj;
lean_object* v_a_483_ = stack[5].m_obj;
lean_object* v_a_484_ = stack[6].m_obj;
lean_object* v_a_485_ = stack[7].m_obj;
lean_object* v_res_519_;
v_res_519_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_478_, v_m_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
stack->m_obj
 = v_res_519_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache___boxed(lean_object* v_e_520_, lean_object* v_m_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_520_, v_m_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec(v_a_522_);
return v_res_529_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(lean_object* v_e_530_, lean_object* v_a_531_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Expr_hasLooseBVars(v_e_530_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_530_, v_a_531_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_530_ = stack[0].m_obj;
lean_object* v_a_531_ = stack[1].m_obj;
lean_object* v_res_537_;
v_res_537_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_530_, v_a_531_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg___boxed(lean_object* v_e_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_e_538_);
return v_res_541_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(lean_object* v_e_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_542_, v_a_544_);
return v___x_550_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_542_ = stack[0].m_obj;
lean_object* v_a_543_ = stack[1].m_obj;
lean_object* v_a_544_ = stack[2].m_obj;
lean_object* v_a_545_ = stack[3].m_obj;
lean_object* v_a_546_ = stack[4].m_obj;
lean_object* v_a_547_ = stack[5].m_obj;
lean_object* v_a_548_ = stack[6].m_obj;
lean_object* v_res_551_;
v_res_551_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(v_e_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___boxed(lean_object* v_e_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(v_e_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_e_552_);
return v_res_560_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(lean_object* v_e_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = l_Lean_Expr_fvarId_x21(v_e_561_);
lean_inc(v___x_566_);
v___x_567_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_566_, v_a_562_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_586_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_586_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
if (lean_obj_tag(v_a_568_) == 1)
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_584_; 
lean_dec(v___x_566_);
v_val_572_ = lean_ctor_get(v_a_568_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_568_);
if (v_isSharedCheck_584_ == 0)
{
v___x_574_ = v_a_568_;
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_a_568_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = l_Lean_LocalDecl_type(v_val_572_);
lean_dec(v_val_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_583_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_e_561_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_579_);
v___x_581_ = v___x_570_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v___x_585_; 
lean_del_object(v___x_570_);
lean_dec(v_a_568_);
lean_dec_ref(v_e_561_);
v___x_585_ = l_Lean_FVarId_throwUnknown___redArg(v___x_566_, v_a_563_, v_a_564_);
return v___x_585_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v___x_566_);
lean_dec_ref(v_e_561_);
v_a_587_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_567_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_567_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_561_ = stack[0].m_obj;
lean_object* v_a_562_ = stack[1].m_obj;
lean_object* v_a_563_ = stack[2].m_obj;
lean_object* v_a_564_ = stack[3].m_obj;
lean_object* v_res_595_;
v_res_595_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_561_, v_a_562_, v_a_563_, v_a_564_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg___boxed(lean_object* v_e_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_a_597_);
return v_res_601_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(lean_object* v_e_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_602_, v_a_603_, v_a_605_, v_a_606_);
return v___x_608_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_602_ = stack[0].m_obj;
lean_object* v_a_603_ = stack[1].m_obj;
lean_object* v_a_604_ = stack[2].m_obj;
lean_object* v_a_605_ = stack[3].m_obj;
lean_object* v_a_606_ = stack[4].m_obj;
lean_object* v_res_609_;
v_res_609_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(v_e_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___boxed(lean_object* v_e_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(v_e_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
return v_res_616_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(lean_object* v_e_617_, lean_object* v___y_618_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = l_Lean_Expr_hasMVar(v_e_617_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_e_617_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; lean_object* v_mctx_623_; lean_object* v___x_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_627_; lean_object* v_cache_628_; lean_object* v_zetaDeltaFVarIds_629_; lean_object* v_postponed_630_; lean_object* v_diag_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_640_; 
v___x_622_ = lean_st_ref_get(v___y_618_);
v_mctx_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_mctx_623_);
lean_dec(v___x_622_);
v___x_624_ = l_Lean_instantiateMVarsCore(v_mctx_623_, v_e_617_);
v_fst_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_fst_625_);
v_snd_626_ = lean_ctor_get(v___x_624_, 1);
lean_inc(v_snd_626_);
lean_dec_ref(v___x_624_);
v___x_627_ = lean_st_ref_take(v___y_618_);
v_cache_628_ = lean_ctor_get(v___x_627_, 1);
v_zetaDeltaFVarIds_629_ = lean_ctor_get(v___x_627_, 2);
v_postponed_630_ = lean_ctor_get(v___x_627_, 3);
v_diag_631_ = lean_ctor_get(v___x_627_, 4);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_627_, 0);
lean_dec(v_unused_641_);
v___x_633_ = v___x_627_;
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_diag_631_);
lean_inc(v_postponed_630_);
lean_inc(v_zetaDeltaFVarIds_629_);
lean_inc(v_cache_628_);
lean_dec(v___x_627_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v_snd_626_);
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_snd_626_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_cache_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_zetaDeltaFVarIds_629_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_postponed_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_diag_631_);
v___x_636_ = v_reuseFailAlloc_639_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_st_ref_put(v___y_618_, v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_fst_625_);
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_617_ = stack[0].m_obj;
lean_object* v___y_618_ = stack[1].m_obj;
lean_object* v_res_642_;
v_res_642_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_617_, v___y_618_);
stack->m_obj
 = v_res_642_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg___boxed(lean_object* v_e_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_643_, v___y_644_);
lean_dec(v___y_644_);
return v_res_646_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(lean_object* v_e_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_647_, v___y_651_);
return v___x_655_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_647_ = stack[0].m_obj;
lean_object* v___y_648_ = stack[1].m_obj;
lean_object* v___y_649_ = stack[2].m_obj;
lean_object* v___y_650_ = stack[3].m_obj;
lean_object* v___y_651_ = stack[4].m_obj;
lean_object* v___y_652_ = stack[5].m_obj;
lean_object* v___y_653_ = stack[6].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(v_e_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___boxed(lean_object* v_e_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(v_e_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
return v_res_665_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(lean_object* v_k_666_, lean_object* v_t_667_){
_start:
{
if (lean_obj_tag(v_t_667_) == 0)
{
lean_object* v_k_668_; lean_object* v_l_669_; lean_object* v_r_670_; uint8_t v___x_671_; 
v_k_668_ = lean_ctor_get(v_t_667_, 1);
v_l_669_ = lean_ctor_get(v_t_667_, 3);
v_r_670_ = lean_ctor_get(v_t_667_, 4);
v___x_671_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_666_, v_k_668_);
switch(v___x_671_)
{
case 0:
{
v_t_667_ = v_l_669_;
goto _start;
}
case 1:
{
uint8_t v___x_673_; 
v___x_673_ = 1;
return v___x_673_;
}
default: 
{
v_t_667_ = v_r_670_;
goto _start;
}
}
}
else
{
uint8_t v___x_675_; 
v___x_675_ = 0;
return v___x_675_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_666_ = stack[0].m_obj;
lean_object* v_t_667_ = stack[1].m_obj;
uint8_t v_res_676_;
v_res_676_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_666_, v_t_667_);
stack->m_num = v_res_676_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg___boxed(lean_object* v_k_677_, lean_object* v_t_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_677_, v_t_678_);
lean_dec(v_t_678_);
lean_dec(v_k_677_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(lean_object* v_as_681_, size_t v_sz_682_, size_t v_i_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_a_691_; uint8_t v___x_695_; 
v___x_695_ = lean_usize_dec_lt(v_i_683_, v_sz_682_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v_b_684_);
return v___x_696_;
}
else
{
lean_object* v_fst_697_; lean_object* v_snd_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_746_; 
v_fst_697_ = lean_ctor_get(v_b_684_, 0);
v_snd_698_ = lean_ctor_get(v_b_684_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_b_684_);
if (v_isSharedCheck_746_ == 0)
{
v___x_700_ = v_b_684_;
v_isShared_701_ = v_isSharedCheck_746_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_snd_698_);
lean_inc(v_fst_697_);
lean_dec(v_b_684_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_746_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_a_702_; uint8_t v___x_703_; 
v_a_702_ = lean_array_uget_borrowed(v_as_681_, v_i_683_);
v___x_703_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_a_702_, v_fst_697_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___x_723_; 
lean_inc_n(v_a_702_, 2);
v___x_704_ = l_Lean_FVarIdSet_insert(v_fst_697_, v_a_702_);
v___x_723_ = l_Lean_FVarId_isLetVar___redArg(v_a_702_, v___x_703_, v___y_685_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; uint8_t v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = lean_unbox(v_a_724_);
lean_dec(v_a_724_);
if (v___x_725_ == 0)
{
v___y_706_ = v___y_685_;
v___y_707_ = v___y_687_;
v___y_708_ = v___y_688_;
goto v___jp_705_;
}
else
{
lean_object* v___x_726_; 
lean_inc(v_a_702_);
v___x_726_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_a_702_, v___y_686_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_dec_ref_known(v___x_726_, 1);
v___y_706_ = v___y_685_;
v___y_707_ = v___y_687_;
v___y_708_ = v___y_688_;
goto v___jp_705_;
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v___x_704_);
lean_del_object(v___x_700_);
lean_dec(v_snd_698_);
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v___x_704_);
lean_del_object(v___x_700_);
lean_dec(v_snd_698_);
v_a_735_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_723_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_723_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
v___jp_705_:
{
lean_object* v___x_709_; 
lean_inc(v_a_702_);
v___x_709_ = l_Lean_FVarId_getType___redArg(v_a_702_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_array_push(v_snd_698_, v_a_710_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_711_);
lean_ctor_set(v___x_700_, 0, v___x_704_);
v___x_713_ = v___x_700_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
v_a_691_ = v___x_713_;
goto v___jp_690_;
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v___x_704_);
lean_del_object(v___x_700_);
lean_dec(v_snd_698_);
v_a_715_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_709_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_709_);
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
}
}
else
{
lean_object* v___x_744_; 
if (v_isShared_701_ == 0)
{
v___x_744_ = v___x_700_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_697_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_snd_698_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
v_a_691_ = v___x_744_;
goto v___jp_690_;
}
}
}
}
v___jp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_683_, v___x_692_);
v_i_683_ = v___x_693_;
v_b_684_ = v_a_691_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_681_ = stack[0].m_obj;
size_t v_sz_682_ = stack[1].m_num;
size_t v_i_683_ = stack[2].m_num;
lean_object* v_b_684_ = stack[3].m_obj;
lean_object* v___y_685_ = stack[4].m_obj;
lean_object* v___y_686_ = stack[5].m_obj;
lean_object* v___y_687_ = stack[6].m_obj;
lean_object* v___y_688_ = stack[7].m_obj;
lean_object* v_res_747_;
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_681_, v_sz_682_, v_i_683_, v_b_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg___boxed(lean_object* v_as_748_, lean_object* v_sz_749_, lean_object* v_i_750_, lean_object* v_b_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_749_);
lean_dec(v_sz_749_);
v_i_boxed_758_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_748_, v_sz_boxed_757_, v_i_boxed_758_, v_b_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec_ref(v_as_748_);
return v_res_759_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_box(0);
v___x_761_ = lean_unsigned_to_nat(16u);
v___x_762_ = lean_mk_array(v___x_761_, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_768_; lean_object* v_visited_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_768_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2));
v_visited_769_ = lean_box(1);
v___x_770_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_visited_769_);
lean_ctor_set(v___x_771_, 2, v___x_768_);
return v___x_771_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object* v_a_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_827_; 
v_fst_780_ = lean_ctor_get(v_a_772_, 0);
v_snd_781_ = lean_ctor_get(v_a_772_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_827_ == 0)
{
v___x_783_ = v_a_772_;
v_isShared_784_ = v_isSharedCheck_827_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
lean_dec(v_a_772_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_827_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = lean_array_get_size(v_snd_781_);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_nat_dec_eq(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_788_ = l_Lean_instInhabitedExpr;
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_sub(v___x_785_, v___x_789_);
v___x_791_ = lean_array_get_borrowed(v___x_788_, v_snd_781_, v___x_790_);
lean_dec(v___x_790_);
lean_inc(v___x_791_);
v___x_792_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v___x_791_, v___y_776_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_fvarIds_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3);
v___x_795_ = l_Lean_collectFVars(v___x_794_, v_a_793_);
v_fvarIds_796_ = lean_ctor_get(v___x_795_, 2);
lean_inc_ref(v_fvarIds_796_);
lean_dec_ref(v___x_795_);
v___x_797_ = lean_array_pop(v_snd_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_797_);
v___x_799_ = v___x_783_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_814_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_sz_800_ = lean_array_size(v_fvarIds_796_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_fvarIds_796_, v_sz_800_, v___x_801_, v___x_799_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec_ref(v_fvarIds_796_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v_fst_804_ = lean_ctor_get(v_a_803_, 0);
v_snd_805_ = lean_ctor_get(v_a_803_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_a_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v_a_803_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_inc(v_fst_804_);
lean_dec(v_a_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_fst_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_snd_805_);
v___x_810_ = v_reuseFailAlloc_812_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v_a_772_ = v___x_810_;
goto _start;
}
}
}
else
{
return v___x_802_;
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_del_object(v___x_783_);
lean_dec(v_snd_781_);
lean_dec(v_fst_780_);
v_a_815_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_792_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_792_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v___x_824_; 
if (v_isShared_784_ == 0)
{
v___x_824_ = v___x_783_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_snd_781_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_772_ = stack[0].m_obj;
lean_object* v___y_773_ = stack[1].m_obj;
lean_object* v___y_774_ = stack[2].m_obj;
lean_object* v___y_775_ = stack[3].m_obj;
lean_object* v___y_776_ = stack[4].m_obj;
lean_object* v___y_777_ = stack[5].m_obj;
lean_object* v___y_778_ = stack[6].m_obj;
lean_object* v_res_828_;
v_res_828_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object* v_a_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
return v_res_837_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object* v_e_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_visited_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_worklist_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_visited_846_ = lean_box(1);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_mk_empty_array_with_capacity(v___x_847_);
v_worklist_849_ = lean_array_push(v___x_848_, v_e_838_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_visited_846_);
lean_ctor_set(v___x_850_, 1, v_worklist_849_);
v___x_851_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v___x_850_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v___x_851_, 0);
lean_dec(v_unused_860_);
v___x_853_ = v___x_851_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_dec(v___x_851_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_box(0);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_851_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_851_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_838_ = stack[0].m_obj;
lean_object* v_a_839_ = stack[1].m_obj;
lean_object* v_a_840_ = stack[2].m_obj;
lean_object* v_a_841_ = stack[3].m_obj;
lean_object* v_a_842_ = stack[4].m_obj;
lean_object* v_a_843_ = stack[5].m_obj;
lean_object* v_a_844_ = stack[6].m_obj;
lean_object* v_res_869_;
v_res_869_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v_e_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object* v_e_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v_e_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec(v_a_871_);
return v_res_878_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object* v_00_u03b2_879_, lean_object* v_k_880_, lean_object* v_t_881_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_880_, v_t_881_);
return v___x_882_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_880_ = stack[1].m_obj;
lean_object* v_t_881_ = stack[2].m_obj;
uint8_t v_res_883_;
v_res_883_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_box(0), v_k_880_, v_t_881_);
stack->m_num = v_res_883_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object* v_00_u03b2_884_, lean_object* v_k_885_, lean_object* v_t_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(v_00_u03b2_884_, v_k_885_, v_t_886_);
lean_dec(v_t_886_);
lean_dec(v_k_885_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object* v_as_889_, size_t v_sz_890_, size_t v_i_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_889_, v_sz_890_, v_i_891_, v_b_892_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_900_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_889_ = stack[0].m_obj;
size_t v_sz_890_ = stack[1].m_num;
size_t v_i_891_ = stack[2].m_num;
lean_object* v_b_892_ = stack[3].m_obj;
lean_object* v___y_893_ = stack[4].m_obj;
lean_object* v___y_894_ = stack[5].m_obj;
lean_object* v___y_895_ = stack[6].m_obj;
lean_object* v___y_896_ = stack[7].m_obj;
lean_object* v___y_897_ = stack[8].m_obj;
lean_object* v___y_898_ = stack[9].m_obj;
lean_object* v_res_901_;
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(v_as_889_, v_sz_890_, v_i_891_, v_b_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object* v_as_902_, lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
size_t v_sz_boxed_913_; size_t v_i_boxed_914_; lean_object* v_res_915_; 
v_sz_boxed_913_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_914_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(v_as_902_, v_sz_boxed_913_, v_i_boxed_914_, v_b_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v_as_902_);
return v_res_915_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_inst_916_, lean_object* v_a_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_917_ = stack[1].m_obj;
lean_object* v___y_918_ = stack[2].m_obj;
lean_object* v___y_919_ = stack[3].m_obj;
lean_object* v___y_920_ = stack[4].m_obj;
lean_object* v___y_921_ = stack[5].m_obj;
lean_object* v___y_922_ = stack[6].m_obj;
lean_object* v___y_923_ = stack[7].m_obj;
lean_object* v_res_926_;
v_res_926_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_box(0), v_a_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_inst_927_, lean_object* v_a_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_inst_927_, v_a_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
return v_res_936_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object* v_mvarId_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v_mctx_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_940_ = lean_st_ref_get(v___y_938_);
v_mctx_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc_ref(v_mctx_941_);
lean_dec(v___x_940_);
v___x_942_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_941_, v_mvarId_937_);
lean_dec_ref(v_mctx_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_937_ = stack[0].m_obj;
lean_object* v___y_938_ = stack[1].m_obj;
lean_object* v_res_944_;
v_res_944_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_937_, v___y_938_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object* v_mvarId_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec(v_mvarId_945_);
return v_res_948_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object* v_mvarId_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_949_, v___y_953_);
return v___x_957_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_949_ = stack[0].m_obj;
lean_object* v___y_950_ = stack[1].m_obj;
lean_object* v___y_951_ = stack[2].m_obj;
lean_object* v___y_952_ = stack[3].m_obj;
lean_object* v___y_953_ = stack[4].m_obj;
lean_object* v___y_954_ = stack[5].m_obj;
lean_object* v___y_955_ = stack[6].m_obj;
lean_object* v_res_958_;
v_res_958_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object* v_mvarId_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v_mvarId_959_);
return v_res_967_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object* v_a_968_, lean_object* v_as_969_, size_t v_sz_970_, size_t v_i_971_, lean_object* v_b_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_a_981_; uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_lt(v_i_971_, v_sz_970_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_a_968_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_b_972_);
return v___x_986_;
}
else
{
lean_object* v_array_987_; lean_object* v_start_988_; lean_object* v_stop_989_; uint8_t v___x_990_; 
v_array_987_ = lean_ctor_get(v_b_972_, 0);
v_start_988_ = lean_ctor_get(v_b_972_, 1);
v_stop_989_ = lean_ctor_get(v_b_972_, 2);
v___x_990_ = lean_nat_dec_lt(v_start_988_, v_stop_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_dec_ref(v_a_968_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_b_972_);
return v___x_991_;
}
else
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1015_; 
lean_inc(v_stop_989_);
lean_inc(v_start_988_);
lean_inc_ref(v_array_987_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_b_972_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1016_ = lean_ctor_get(v_b_972_, 2);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_b_972_, 1);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_b_972_, 0);
lean_dec(v_unused_1018_);
v___x_993_ = v_b_972_;
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
else
{
lean_dec(v_b_972_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_lctx_995_; lean_object* v___x_996_; lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v_lctx_995_ = lean_ctor_get(v_a_968_, 1);
v___x_996_ = lean_array_fget(v_array_987_, v_start_988_);
v_a_997_ = lean_array_uget_borrowed(v_as_969_, v_i_971_);
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_nat_add(v_start_988_, v___x_998_);
lean_dec(v_start_988_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_999_);
v___x_1001_ = v___x_993_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_array_987_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_stop_989_);
v___x_1001_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; uint8_t v___x_1004_; 
lean_inc_ref(v_lctx_995_);
v___x_1002_ = l_Lean_LocalContext_getFVar_x21(v_lctx_995_, v_a_997_);
v___x_1003_ = 0;
v___x_1004_ = l_Lean_LocalDecl_isLet(v___x_1002_, v___x_1003_);
lean_dec_ref(v___x_1002_);
if (v___x_1004_ == 0)
{
lean_dec(v___x_996_);
v_a_981_ = v___x_1001_;
goto v___jp_980_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v___x_996_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_dec_ref_known(v___x_1005_, 1);
v_a_981_ = v___x_1001_;
goto v___jp_980_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v___x_1001_);
lean_dec_ref(v_a_968_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
}
}
v___jp_980_:
{
size_t v___x_982_; size_t v___x_983_; 
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_971_, v___x_982_);
v_i_971_ = v___x_983_;
v_b_972_ = v_a_981_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_968_ = stack[0].m_obj;
lean_object* v_as_969_ = stack[1].m_obj;
size_t v_sz_970_ = stack[2].m_num;
size_t v_i_971_ = stack[3].m_num;
lean_object* v_b_972_ = stack[4].m_obj;
lean_object* v___y_973_ = stack[5].m_obj;
lean_object* v___y_974_ = stack[6].m_obj;
lean_object* v___y_975_ = stack[7].m_obj;
lean_object* v___y_976_ = stack[8].m_obj;
lean_object* v___y_977_ = stack[9].m_obj;
lean_object* v___y_978_ = stack[10].m_obj;
lean_object* v_res_1019_;
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_968_, v_as_969_, v_sz_970_, v_i_971_, v_b_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
stack->m_obj
 = v_res_1019_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object* v_a_1020_, lean_object* v_as_1021_, lean_object* v_sz_1022_, lean_object* v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
size_t v_sz_boxed_1032_; size_t v_i_boxed_1033_; lean_object* v_res_1034_; 
v_sz_boxed_1032_ = lean_unbox_usize(v_sz_1022_);
lean_dec(v_sz_1022_);
v_i_boxed_1033_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1020_, v_as_1021_, v_sz_boxed_1032_, v_i_boxed_1033_, v_b_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v_as_1021_);
return v_res_1034_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object* v_as_1035_, lean_object* v___y_1036_){
_start:
{
if (lean_obj_tag(v_as_1035_) == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
else
{
lean_object* v_head_1040_; lean_object* v_tail_1041_; lean_object* v___x_1042_; 
v_head_1040_ = lean_ctor_get(v_as_1035_, 0);
lean_inc(v_head_1040_);
v_tail_1041_ = lean_ctor_get(v_as_1035_, 1);
lean_inc(v_tail_1041_);
lean_dec_ref_known(v_as_1035_, 2);
v___x_1042_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_head_1040_, v___y_1036_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref_known(v___x_1042_, 1);
v_as_1035_ = v_tail_1041_;
goto _start;
}
else
{
lean_dec(v_tail_1041_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1035_ = stack[0].m_obj;
lean_object* v___y_1036_ = stack[1].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1035_, v___y_1036_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object* v_as_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1045_, v___y_1046_);
lean_dec(v___y_1046_);
return v_res_1048_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object* v_mvarId_1049_, lean_object* v_args_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1115_; 
v___x_1058_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1049_, v_a_1054_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1115_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1115_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
if (lean_obj_tag(v_a_1059_) == 1)
{
lean_object* v_val_1063_; lean_object* v_fvars_1064_; lean_object* v_mvarIdPending_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
lean_del_object(v___x_1061_);
v_val_1063_ = lean_ctor_get(v_a_1059_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v_a_1059_, 1);
v_fvars_1064_ = lean_ctor_get(v_val_1063_, 0);
lean_inc_ref(v_fvars_1064_);
v_mvarIdPending_1065_ = lean_ctor_get(v_val_1063_, 1);
lean_inc(v_mvarIdPending_1065_);
lean_dec(v_val_1063_);
v___x_1066_ = lean_array_get_size(v_fvars_1064_);
v___x_1067_ = lean_array_get_size(v_args_1050_);
v___x_1068_ = lean_nat_dec_le(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec(v_mvarIdPending_1065_);
lean_dec_ref(v_fvars_1064_);
lean_dec_ref(v_args_1050_);
lean_inc(v_a_1051_);
v___x_1069_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_a_1051_, v_a_1054_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1077_; 
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___x_1069_, 0);
lean_dec(v_unused_1078_);
v___x_1071_ = v___x_1069_;
v_isShared_1072_ = v_isSharedCheck_1077_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v___x_1069_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1077_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = lean_box(0);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1073_);
v___x_1075_ = v___x_1071_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
else
{
return v___x_1069_;
}
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_MVarId_getDecl(v_mvarIdPending_1065_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; size_t v_sz_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = l_Array_toSubarray___redArg(v_args_1050_, v___x_1081_, v___x_1067_);
v_sz_1083_ = lean_array_size(v_fvars_1064_);
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1080_, v_fvars_1064_, v_sz_1083_, v___x_1084_, v___x_1082_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec_ref(v_fvars_1064_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v___x_1085_, 0);
lean_dec(v_unused_1094_);
v___x_1087_ = v___x_1085_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v___x_1085_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1085_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1085_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v_fvars_1064_);
lean_dec_ref(v_args_1050_);
v_a_1103_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1079_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1079_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec(v_a_1059_);
lean_dec_ref(v_args_1050_);
v___x_1111_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1111_);
v___x_1113_ = v___x_1061_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1049_ = stack[0].m_obj;
lean_object* v_args_1050_ = stack[1].m_obj;
lean_object* v_a_1051_ = stack[2].m_obj;
lean_object* v_a_1052_ = stack[3].m_obj;
lean_object* v_a_1053_ = stack[4].m_obj;
lean_object* v_a_1054_ = stack[5].m_obj;
lean_object* v_a_1055_ = stack[6].m_obj;
lean_object* v_a_1056_ = stack[7].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1049_, v_args_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object* v_mvarId_1117_, lean_object* v_args_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1117_, v_args_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec(v_mvarId_1117_);
return v_res_1126_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object* v_as_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1127_, v___y_1131_);
return v___x_1135_;
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1127_ = stack[0].m_obj;
lean_object* v___y_1128_ = stack[1].m_obj;
lean_object* v___y_1129_ = stack[2].m_obj;
lean_object* v___y_1130_ = stack[3].m_obj;
lean_object* v___y_1131_ = stack[4].m_obj;
lean_object* v___y_1132_ = stack[5].m_obj;
lean_object* v___y_1133_ = stack[6].m_obj;
lean_object* v_res_1136_;
v_res_1136_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
stack->m_obj
 = v_res_1136_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object* v_as_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
return v_res_1145_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object* v_e_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = l_Lean_Expr_mvarId_x21(v_e_1148_);
v___x_1157_ = l_Lean_MVarId_findDecl_x3f___redArg(v___x_1156_, v_a_1152_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1188_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
if (lean_obj_tag(v_a_1158_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1186_; 
v_val_1162_ = lean_ctor_get(v_a_1158_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_a_1158_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1164_ = v_a_1158_;
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_val_1162_);
lean_dec(v_a_1158_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
uint8_t v___x_1175_; 
v___x_1175_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1149_);
if (v___x_1175_ == 0)
{
lean_dec(v___x_1156_);
goto v___jp_1166_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_1177_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v___x_1156_, v___x_1176_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v___x_1156_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_dec_ref_known(v___x_1177_, 1);
goto v___jp_1166_;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_del_object(v___x_1164_);
lean_dec(v_val_1162_);
lean_del_object(v___x_1160_);
lean_dec_ref(v_e_1148_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
v___jp_1166_:
{
lean_object* v_type_1167_; lean_object* v___x_1169_; 
v_type_1167_ = lean_ctor_get(v_val_1162_, 2);
lean_inc_ref(v_type_1167_);
lean_dec(v_val_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v_type_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_type_1167_);
v___x_1169_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_e_1148_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1170_);
v___x_1172_ = v___x_1160_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
else
{
lean_object* v___x_1187_; 
lean_del_object(v___x_1160_);
lean_dec(v_a_1158_);
lean_dec_ref(v_e_1148_);
v___x_1187_ = l_Lean_Meta_throwUnknownMVar___redArg(v___x_1156_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v___x_1156_);
lean_dec_ref(v_e_1148_);
v_a_1189_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1157_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1157_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1148_ = stack[0].m_obj;
lean_object* v_a_1149_ = stack[1].m_obj;
lean_object* v_a_1150_ = stack[2].m_obj;
lean_object* v_a_1151_ = stack[3].m_obj;
lean_object* v_a_1152_ = stack[4].m_obj;
lean_object* v_a_1153_ = stack[5].m_obj;
lean_object* v_a_1154_ = stack[6].m_obj;
lean_object* v_res_1197_;
v_res_1197_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
stack->m_obj
 = v_res_1197_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object* v_e_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec(v_a_1199_);
return v_res_1206_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_instMonadEIO___redArg();
return v___x_1207_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_toApplicative_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1285_; 
v___x_1220_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0);
v___x_1221_ = l_StateRefT_x27_instMonad___redArg(v___x_1220_);
v_toApplicative_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1221_, 1);
lean_dec(v_unused_1286_);
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1285_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_toApplicative_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1285_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_toFunctor_1226_; lean_object* v_toSeq_1227_; lean_object* v_toSeqLeft_1228_; lean_object* v_toSeqRight_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1283_; 
v_toFunctor_1226_ = lean_ctor_get(v_toApplicative_1222_, 0);
v_toSeq_1227_ = lean_ctor_get(v_toApplicative_1222_, 2);
v_toSeqLeft_1228_ = lean_ctor_get(v_toApplicative_1222_, 3);
v_toSeqRight_1229_ = lean_ctor_get(v_toApplicative_1222_, 4);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_toApplicative_1222_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_toApplicative_1222_, 1);
lean_dec(v_unused_1284_);
v___x_1231_ = v_toApplicative_1222_;
v_isShared_1232_ = v_isSharedCheck_1283_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_toSeqRight_1229_);
lean_inc(v_toSeqLeft_1228_);
lean_inc(v_toSeq_1227_);
lean_inc(v_toFunctor_1226_);
lean_dec(v_toApplicative_1222_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1283_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1242_; 
v___f_1233_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1));
v___f_1234_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1226_);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toFunctor_1226_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toFunctor_1226_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___f_1235_);
lean_ctor_set(v___x_1237_, 1, v___f_1236_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toSeqRight_1229_);
v___f_1239_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1239_, 0, v_toSeqLeft_1228_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeq_1227_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___f_1238_);
lean_ctor_set(v___x_1231_, 3, v___f_1239_);
lean_ctor_set(v___x_1231_, 2, v___f_1240_);
lean_ctor_set(v___x_1231_, 1, v___f_1233_);
lean_ctor_set(v___x_1231_, 0, v___x_1237_);
v___x_1242_ = v___x_1231_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___f_1233_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v___f_1240_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v___f_1239_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v___f_1238_);
v___x_1242_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___f_1234_);
lean_ctor_set(v___x_1224_, 0, v___x_1242_);
v___x_1244_ = v___x_1224_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___f_1234_);
v___x_1244_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v_toApplicative_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1279_; 
v___x_1245_ = l_StateRefT_x27_instMonad___redArg(v___x_1244_);
v_toApplicative_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1245_, 1);
lean_dec(v_unused_1280_);
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1279_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_toApplicative_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1279_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_toFunctor_1250_; lean_object* v_toSeq_1251_; lean_object* v_toSeqLeft_1252_; lean_object* v_toSeqRight_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1277_; 
v_toFunctor_1250_ = lean_ctor_get(v_toApplicative_1246_, 0);
v_toSeq_1251_ = lean_ctor_get(v_toApplicative_1246_, 2);
v_toSeqLeft_1252_ = lean_ctor_get(v_toApplicative_1246_, 3);
v_toSeqRight_1253_ = lean_ctor_get(v_toApplicative_1246_, 4);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_toApplicative_1246_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_toApplicative_1246_, 1);
lean_dec(v_unused_1278_);
v___x_1255_ = v_toApplicative_1246_;
v_isShared_1256_ = v_isSharedCheck_1277_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_toSeqRight_1253_);
lean_inc(v_toSeqLeft_1252_);
lean_inc(v_toSeq_1251_);
lean_inc(v_toFunctor_1250_);
lean_dec(v_toApplicative_1246_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1277_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1266_; 
v___f_1257_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3));
v___f_1258_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1250_);
v___f_1259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1259_, 0, v_toFunctor_1250_);
v___f_1260_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1260_, 0, v_toFunctor_1250_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___f_1259_);
lean_ctor_set(v___x_1261_, 1, v___f_1260_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toSeqRight_1253_);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toSeqLeft_1252_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toSeq_1251_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___f_1262_);
lean_ctor_set(v___x_1255_, 3, v___f_1263_);
lean_ctor_set(v___x_1255_, 2, v___f_1264_);
lean_ctor_set(v___x_1255_, 1, v___f_1257_);
lean_ctor_set(v___x_1255_, 0, v___x_1261_);
v___x_1266_ = v___x_1255_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___f_1257_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v___f_1264_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___f_1263_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___f_1262_);
v___x_1266_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v___f_1258_);
lean_ctor_set(v___x_1248_, 0, v___x_1266_);
v___x_1268_ = v___x_1248_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___f_1258_);
v___x_1268_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___x_1420__overap_1273_; lean_object* v___x_1274_; 
v___x_1269_ = l_StateRefT_x27_instMonad___redArg(v___x_1268_);
v___x_1270_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1271_ = l_instInhabitedOfMonad___redArg(v___x_1269_, v___x_1270_);
v___f_1272_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1272_, 0, v___x_1271_);
v___x_1420__overap_1273_ = lean_panic_fn_borrowed(v___f_1272_, v_msg_1212_);
lean_dec_ref(v___f_1272_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___y_1213_);
v___x_1274_ = lean_apply_7(v___x_1420__overap_1273_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, lean_box(0));
return v___x_1274_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1212_ = stack[0].m_obj;
lean_object* v___y_1213_ = stack[1].m_obj;
lean_object* v___y_1214_ = stack[2].m_obj;
lean_object* v___y_1215_ = stack[3].m_obj;
lean_object* v___y_1216_ = stack[4].m_obj;
lean_object* v___y_1217_ = stack[5].m_obj;
lean_object* v___y_1218_ = stack[6].m_obj;
lean_object* v_res_1287_;
v_res_1287_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
stack->m_obj
 = v_res_1287_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object* v_msg_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec(v___y_1289_);
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1300_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1301_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
lean_ctor_set(v___x_1303_, 2, v___x_1302_);
lean_ctor_set(v___x_1303_, 3, v___x_1302_);
lean_ctor_set(v___x_1303_, 4, v___x_1301_);
lean_ctor_set(v___x_1303_, 5, v___x_1301_);
lean_ctor_set(v___x_1303_, 6, v___x_1301_);
lean_ctor_set(v___x_1303_, 7, v___x_1301_);
lean_ctor_set(v___x_1303_, 8, v___x_1301_);
lean_ctor_set(v___x_1303_, 9, v___x_1301_);
lean_ctor_set(v___x_1303_, 10, v___x_1301_);
lean_ctor_set(v___x_1303_, 11, v___x_1300_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_unsigned_to_nat(32u);
v___x_1305_ = lean_mk_empty_array_with_capacity(v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1307_ = ((size_t)5ULL);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_unsigned_to_nat(32u);
v___x_1310_ = lean_mk_empty_array_with_capacity(v___x_1309_);
v___x_1311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1312_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v___x_1308_);
lean_ctor_set(v___x_1312_, 3, v___x_1308_);
lean_ctor_set_usize(v___x_1312_, 4, v___x_1307_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1313_ = lean_box(1);
v___x_1314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___x_1314_);
lean_ctor_set(v___x_1316_, 2, v___x_1313_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__22));
v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__24));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__26));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1350_, lean_object* v_declHint_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v_env_1356_; uint8_t v___x_1357_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_st_ref_get(v___y_1352_);
v_env_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_ref(v_env_1356_);
lean_dec(v___x_1355_);
v___x_1357_ = l_Lean_Name_isAnonymous(v_declHint_1351_);
if (v___x_1357_ == 0)
{
uint8_t v_isExporting_1358_; 
v_isExporting_1358_ = lean_ctor_get_uint8(v_env_1356_, sizeof(void*)*13);
if (v_isExporting_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v_env_1356_);
lean_dec(v_declHint_1351_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_msg_1350_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
lean_inc_ref(v_env_1356_);
v___x_1360_ = l_Lean_Environment_setExporting(v_env_1356_, v___x_1357_);
lean_inc(v_declHint_1351_);
lean_inc_ref(v___x_1360_);
v___x_1361_ = l_Lean_Environment_contains(v___x_1360_, v_declHint_1351_, v_isExporting_1358_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec_ref(v___x_1360_);
lean_dec_ref(v_env_1356_);
lean_dec(v_declHint_1351_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_msg_1350_);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_c_1368_; lean_object* v___x_1369_; 
v___x_1363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1365_ = l_Lean_Options_empty;
v___x_1366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1360_);
lean_ctor_set(v___x_1366_, 1, v___x_1363_);
lean_ctor_set(v___x_1366_, 2, v___x_1364_);
lean_ctor_set(v___x_1366_, 3, v___x_1365_);
lean_inc(v_declHint_1351_);
v___x_1367_ = l_Lean_MessageData_ofConstName(v_declHint_1351_, v___x_1357_);
v_c_1368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1368_, 0, v___x_1366_);
lean_ctor_set(v_c_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1356_, v_declHint_1351_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v_env_1356_);
lean_dec(v_declHint_1351_);
v___x_1370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v_c_1368_);
v___x_1372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_MessageData_note(v___x_1373_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_msg_1350_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v_val_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1433_; 
v_val_1377_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1379_ = v___x_1369_;
v_isShared_1380_ = v_isSharedCheck_1433_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_val_1377_);
lean_dec(v___x_1369_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1433_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v_modules_1382_; lean_object* v_moduleNames_1383_; lean_object* v_mod_1384_; uint8_t v___y_1386_; uint8_t v___x_1416_; 
v___x_1381_ = l_Lean_Environment_header(v_env_1356_);
lean_dec_ref(v_env_1356_);
v_modules_1382_ = lean_ctor_get(v___x_1381_, 3);
lean_inc_ref(v_modules_1382_);
v_moduleNames_1383_ = lean_ctor_get(v___x_1381_, 4);
lean_inc_ref(v_moduleNames_1383_);
lean_dec_ref(v___x_1381_);
v_mod_1384_ = lean_array_get(v___x_1354_, v_moduleNames_1383_, v_val_1377_);
lean_dec_ref(v_moduleNames_1383_);
v___x_1416_ = l_Lean_isPrivateName(v_declHint_1351_);
lean_dec(v_declHint_1351_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = lean_array_get_size(v_modules_1382_);
v___x_1418_ = lean_nat_dec_lt(v_val_1377_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v_modules_1382_);
lean_dec(v_val_1377_);
v___y_1386_ = v___x_1416_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1419_; lean_object* v_toImport_1420_; uint8_t v_isExported_1421_; 
v___x_1419_ = lean_array_fget(v_modules_1382_, v_val_1377_);
lean_dec(v_val_1377_);
lean_dec_ref(v_modules_1382_);
v_toImport_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_toImport_1420_);
lean_dec(v___x_1419_);
v_isExported_1421_ = lean_ctor_get_uint8(v_toImport_1420_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1420_);
v___y_1386_ = v_isExported_1421_;
goto v___jp_1385_;
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_modules_1382_);
lean_del_object(v___x_1379_);
lean_dec(v_val_1377_);
v___x_1422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v_c_1368_);
v___x_1424_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = l_Lean_MessageData_ofName(v_mod_1384_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l_Lean_MessageData_note(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_msg_1350_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
v___jp_1385_:
{
if (v___y_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
lean_ctor_set(v___x_1388_, 1, v_c_1368_);
v___x_1389_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = l_Lean_MessageData_ofName(v_mod_1384_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = l_Lean_MessageData_note(v___x_1394_);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_msg_1350_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1396_);
v___x_1398_ = v___x_1379_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1400_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v_c_1368_);
v___x_1402_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_MessageData_ofName(v_mod_1384_);
lean_inc_ref(v___x_1404_);
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v___x_1404_);
v___x_1409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_MessageData_note(v___x_1410_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_msg_1350_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1412_);
v___x_1414_ = v___x_1379_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
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
lean_object* v___x_1434_; 
lean_dec_ref(v_env_1356_);
lean_dec(v_declHint_1351_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_msg_1350_);
return v___x_1434_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1350_ = stack[0].m_obj;
lean_object* v_declHint_1351_ = stack[1].m_obj;
lean_object* v___y_1352_ = stack[2].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1350_, v_declHint_1351_, v___y_1352_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1436_, lean_object* v_declHint_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1436_, v_declHint_1437_, v___y_1438_);
lean_dec(v___y_1438_);
return v_res_1440_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1441_, lean_object* v_declHint_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
v___x_1450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1441_, v_declHint_1442_, v___y_1448_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1455_ = l_Lean_unknownIdentifierMessageTag;
v___x_1456_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v_a_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1441_ = stack[0].m_obj;
lean_object* v_declHint_1442_ = stack[1].m_obj;
lean_object* v___y_1443_ = stack[2].m_obj;
lean_object* v___y_1444_ = stack[3].m_obj;
lean_object* v___y_1445_ = stack[4].m_obj;
lean_object* v___y_1446_ = stack[5].m_obj;
lean_object* v___y_1447_ = stack[6].m_obj;
lean_object* v___y_1448_ = stack[7].m_obj;
lean_object* v_res_1461_;
v_res_1461_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1441_, v_declHint_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
stack->m_obj
 = v_res_1461_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1462_, lean_object* v_declHint_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1462_, v_declHint_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
return v_res_1471_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v_env_1479_; uint8_t v___x_1480_; lean_object* v_env_1481_; lean_object* v___x_1482_; lean_object* v_toCold_1483_; lean_object* v_mctx_1484_; lean_object* v_lctx_1485_; lean_object* v_options_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1478_ = lean_st_ref_get(v___y_1476_);
v_env_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc_ref(v_env_1479_);
lean_dec(v___x_1478_);
v___x_1480_ = 0;
v_env_1481_ = l_Lean_Environment_setRecordingDeps(v_env_1479_, v___x_1480_);
v___x_1482_ = lean_st_ref_get(v___y_1474_);
v_toCold_1483_ = lean_ctor_get(v___y_1475_, 0);
v_mctx_1484_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_ref(v_mctx_1484_);
lean_dec(v___x_1482_);
v_lctx_1485_ = lean_ctor_get(v___y_1473_, 2);
v_options_1486_ = lean_ctor_get(v_toCold_1483_, 2);
lean_inc_ref(v_options_1486_);
lean_inc_ref(v_lctx_1485_);
v___x_1487_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1487_, 0, v_env_1481_);
lean_ctor_set(v___x_1487_, 1, v_mctx_1484_);
lean_ctor_set(v___x_1487_, 2, v_lctx_1485_);
lean_ctor_set(v___x_1487_, 3, v_options_1486_);
v___x_1488_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_msgData_1472_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1472_ = stack[0].m_obj;
lean_object* v___y_1473_ = stack[1].m_obj;
lean_object* v___y_1474_ = stack[2].m_obj;
lean_object* v___y_1475_ = stack[3].m_obj;
lean_object* v___y_1476_ = stack[4].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1497_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_ref_1504_; lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1514_; 
v_ref_1504_ = lean_ctor_get(v___y_1501_, 2);
v___x_1505_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_inc(v_ref_1504_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_ref_1504_);
lean_ctor_set(v___x_1510_, 1, v_a_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 1);
lean_ctor_set(v___x_1508_, 0, v___x_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1498_ = stack[0].m_obj;
lean_object* v___y_1499_ = stack[1].m_obj;
lean_object* v___y_1500_ = stack[2].m_obj;
lean_object* v___y_1501_ = stack[3].m_obj;
lean_object* v___y_1502_ = stack[4].m_obj;
lean_object* v_res_1515_;
v_res_1515_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
stack->m_obj
 = v_res_1515_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1522_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_toCold_1532_; lean_object* v_currRecDepth_1533_; lean_object* v_ref_1534_; uint16_t v_optionFlags_1535_; uint8_t v_suppressElabErrors_1536_; uint8_t v_isRecordingDeps_1537_; lean_object* v_ref_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_toCold_1532_ = lean_ctor_get(v___y_1529_, 0);
v_currRecDepth_1533_ = lean_ctor_get(v___y_1529_, 1);
v_ref_1534_ = lean_ctor_get(v___y_1529_, 2);
v_optionFlags_1535_ = lean_ctor_get_uint16(v___y_1529_, sizeof(void*)*3);
v_suppressElabErrors_1536_ = lean_ctor_get_uint8(v___y_1529_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1537_ = lean_ctor_get_uint8(v___y_1529_, sizeof(void*)*3 + 3);
v_ref_1538_ = l_Lean_replaceRef(v_ref_1523_, v_ref_1534_);
lean_inc(v_currRecDepth_1533_);
lean_inc_ref(v_toCold_1532_);
v___x_1539_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1539_, 0, v_toCold_1532_);
lean_ctor_set(v___x_1539_, 1, v_currRecDepth_1533_);
lean_ctor_set(v___x_1539_, 2, v_ref_1538_);
lean_ctor_set_uint16(v___x_1539_, sizeof(void*)*3, v_optionFlags_1535_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*3 + 2, v_suppressElabErrors_1536_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*3 + 3, v_isRecordingDeps_1537_);
v___x_1540_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1524_, v___y_1527_, v___y_1528_, v___x_1539_, v___y_1530_);
lean_dec_ref_known(v___x_1539_, 3);
return v___x_1540_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1523_ = stack[0].m_obj;
lean_object* v_msg_1524_ = stack[1].m_obj;
lean_object* v___y_1525_ = stack[2].m_obj;
lean_object* v___y_1526_ = stack[3].m_obj;
lean_object* v___y_1527_ = stack[4].m_obj;
lean_object* v___y_1528_ = stack[5].m_obj;
lean_object* v___y_1529_ = stack[6].m_obj;
lean_object* v___y_1530_ = stack[7].m_obj;
lean_object* v_res_1541_;
v_res_1541_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1523_, v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
stack->m_obj
 = v_res_1541_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1542_, lean_object* v_msg_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1542_, v_msg_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v_ref_1542_);
return v_res_1551_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1552_, lean_object* v_msg_1553_, lean_object* v_declHint_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v_a_1563_; lean_object* v___x_1564_; 
v___x_1562_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1553_, v_declHint_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1552_, v_a_1563_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1564_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1552_ = stack[0].m_obj;
lean_object* v_msg_1553_ = stack[1].m_obj;
lean_object* v_declHint_1554_ = stack[2].m_obj;
lean_object* v___y_1555_ = stack[3].m_obj;
lean_object* v___y_1556_ = stack[4].m_obj;
lean_object* v___y_1557_ = stack[5].m_obj;
lean_object* v___y_1558_ = stack[6].m_obj;
lean_object* v___y_1559_ = stack[7].m_obj;
lean_object* v___y_1560_ = stack[8].m_obj;
lean_object* v_res_1565_;
v_res_1565_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1552_, v_msg_1553_, v_declHint_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
stack->m_obj
 = v_res_1565_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1566_, lean_object* v_msg_1567_, lean_object* v_declHint_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1566_, v_msg_1567_, v_declHint_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v_ref_1566_);
return v_res_1576_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1579_ = l_Lean_stringToMessageData(v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1583_, lean_object* v_constName_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1592_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1593_ = 0;
lean_inc(v_constName_1584_);
v___x_1594_ = l_Lean_MessageData_ofConstName(v_constName_1584_, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1592_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1583_, v___x_1597_, v_constName_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1598_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1583_ = stack[0].m_obj;
lean_object* v_constName_1584_ = stack[1].m_obj;
lean_object* v___y_1585_ = stack[2].m_obj;
lean_object* v___y_1586_ = stack[3].m_obj;
lean_object* v___y_1587_ = stack[4].m_obj;
lean_object* v___y_1588_ = stack[5].m_obj;
lean_object* v___y_1589_ = stack[6].m_obj;
lean_object* v___y_1590_ = stack[7].m_obj;
lean_object* v_res_1599_;
v_res_1599_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1583_, v_constName_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
stack->m_obj
 = v_res_1599_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1600_, lean_object* v_constName_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1600_, v_constName_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec(v_ref_1600_);
return v_res_1609_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_ref_1618_; lean_object* v___x_1619_; 
v_ref_1618_ = lean_ctor_get(v___y_1615_, 2);
v___x_1619_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1618_, v_constName_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
return v___x_1619_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1610_ = stack[0].m_obj;
lean_object* v___y_1611_ = stack[1].m_obj;
lean_object* v___y_1612_ = stack[2].m_obj;
lean_object* v___y_1613_ = stack[3].m_obj;
lean_object* v___y_1614_ = stack[4].m_obj;
lean_object* v___y_1615_ = stack[5].m_obj;
lean_object* v___y_1616_ = stack[6].m_obj;
lean_object* v_res_1620_;
v_res_1620_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
stack->m_obj
 = v_res_1620_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v___y_1622_);
return v_res_1629_;
}
}
lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_env_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_st_ref_get(v___y_1636_);
v_env_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_env_1639_);
lean_dec(v___x_1638_);
v___x_1640_ = 0;
lean_inc(v_constName_1630_);
v___x_1641_ = l_Lean_Environment_findConstVal_x3f(v_env_1639_, v_constName_1630_, v___x_1640_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1642_;
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_constName_1630_);
v_val_1643_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1641_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_val_1643_);
lean_dec(v___x_1641_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 0);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1630_ = stack[0].m_obj;
lean_object* v___y_1631_ = stack[1].m_obj;
lean_object* v___y_1632_ = stack[2].m_obj;
lean_object* v___y_1633_ = stack[3].m_obj;
lean_object* v___y_1634_ = stack[4].m_obj;
lean_object* v___y_1635_ = stack[5].m_obj;
lean_object* v___y_1636_ = stack[6].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec(v___y_1653_);
return v_res_1660_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1665_ = lean_unsigned_to_nat(35u);
v___x_1666_ = lean_unsigned_to_nat(203u);
v___x_1667_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1669_ = l_mkPanicMessageWithDecl(v___x_1668_, v___x_1667_, v___x_1666_, v___x_1665_, v___x_1664_);
return v___x_1669_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
if (lean_obj_tag(v_e_1670_) == 4)
{
lean_object* v_declName_1678_; lean_object* v_us_1679_; lean_object* v___x_1680_; 
v_declName_1678_ = lean_ctor_get(v_e_1670_, 0);
v_us_1679_ = lean_ctor_get(v_e_1670_, 1);
lean_inc(v_declName_1678_);
v___x_1680_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1678_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v_levelParams_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v_levelParams_1682_ = lean_ctor_get(v_a_1681_, 1);
v___x_1683_ = l_List_lengthTR___redArg(v_levelParams_1682_);
v___x_1684_ = l_List_lengthTR___redArg(v_us_1679_);
v___x_1685_ = lean_nat_dec_eq(v___x_1683_, v___x_1684_);
lean_dec(v___x_1684_);
lean_dec(v___x_1683_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
lean_inc(v_us_1679_);
lean_inc(v_declName_1678_);
lean_dec(v_a_1681_);
lean_dec_ref_known(v_e_1670_, 2);
v___x_1686_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1678_, v_us_1679_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; 
lean_inc(v_us_1679_);
v___x_1687_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1681_, v_us_1679_, v___y_1676_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1697_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_a_1688_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_e_1670_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1693_);
v___x_1695_ = v___x_1690_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref_known(v_e_1670_, 2);
v_a_1698_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1687_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1687_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref_known(v_e_1670_, 2);
v_a_1706_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1680_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1680_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v_e_1670_);
v___x_1714_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1715_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1714_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1715_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1670_ = stack[0].m_obj;
lean_object* v___y_1671_ = stack[1].m_obj;
lean_object* v___y_1672_ = stack[2].m_obj;
lean_object* v___y_1673_ = stack[3].m_obj;
lean_object* v___y_1674_ = stack[4].m_obj;
lean_object* v___y_1675_ = stack[5].m_obj;
lean_object* v___y_1676_ = stack[6].m_obj;
lean_object* v_res_1716_;
v_res_1716_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
stack->m_obj
 = v_res_1716_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v___y_1718_);
return v_res_1725_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___y_1734_; lean_object* v___x_1735_; 
lean_inc_ref(v_e_1726_);
v___y_1734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1734_, 0, v_e_1726_);
v___x_1735_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1726_, v___y_1734_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1726_ = stack[0].m_obj;
lean_object* v_a_1727_ = stack[1].m_obj;
lean_object* v_a_1728_ = stack[2].m_obj;
lean_object* v_a_1729_ = stack[3].m_obj;
lean_object* v_a_1730_ = stack[4].m_obj;
lean_object* v_a_1731_ = stack[5].m_obj;
lean_object* v_a_1732_ = stack[6].m_obj;
lean_object* v_res_1736_;
v_res_1736_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
stack->m_obj
 = v_res_1736_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec(v_a_1738_);
return v_res_1745_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1746_, lean_object* v_constName_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1747_ = stack[1].m_obj;
lean_object* v___y_1748_ = stack[2].m_obj;
lean_object* v___y_1749_ = stack[3].m_obj;
lean_object* v___y_1750_ = stack[4].m_obj;
lean_object* v___y_1751_ = stack[5].m_obj;
lean_object* v___y_1752_ = stack[6].m_obj;
lean_object* v___y_1753_ = stack[7].m_obj;
lean_object* v_res_1756_;
v_res_1756_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_box(0), v_constName_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
stack->m_obj
 = v_res_1756_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_constName_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1757_, v_constName_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec(v___y_1759_);
return v_res_1766_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1767_, lean_object* v_ref_1768_, lean_object* v_constName_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1768_, v_constName_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1768_ = stack[1].m_obj;
lean_object* v_constName_1769_ = stack[2].m_obj;
lean_object* v___y_1770_ = stack[3].m_obj;
lean_object* v___y_1771_ = stack[4].m_obj;
lean_object* v___y_1772_ = stack[5].m_obj;
lean_object* v___y_1773_ = stack[6].m_obj;
lean_object* v___y_1774_ = stack[7].m_obj;
lean_object* v___y_1775_ = stack[8].m_obj;
lean_object* v_res_1778_;
v_res_1778_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_box(0), v_ref_1768_, v_constName_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
stack->m_obj
 = v_res_1778_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_ref_1780_, lean_object* v_constName_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1779_, v_ref_1780_, v_constName_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v_ref_1780_);
return v_res_1789_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1790_, lean_object* v_ref_1791_, lean_object* v_msg_1792_, lean_object* v_declHint_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1791_, v_msg_1792_, v_declHint_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1791_ = stack[1].m_obj;
lean_object* v_msg_1792_ = stack[2].m_obj;
lean_object* v_declHint_1793_ = stack[3].m_obj;
lean_object* v___y_1794_ = stack[4].m_obj;
lean_object* v___y_1795_ = stack[5].m_obj;
lean_object* v___y_1796_ = stack[6].m_obj;
lean_object* v___y_1797_ = stack[7].m_obj;
lean_object* v___y_1798_ = stack[8].m_obj;
lean_object* v___y_1799_ = stack[9].m_obj;
lean_object* v_res_1802_;
v_res_1802_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_box(0), v_ref_1791_, v_msg_1792_, v_declHint_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
stack->m_obj
 = v_res_1802_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_ref_1804_, lean_object* v_msg_1805_, lean_object* v_declHint_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1803_, v_ref_1804_, v_msg_1805_, v_declHint_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec(v_ref_1804_);
return v_res_1814_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1815_, lean_object* v_declHint_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1815_, v_declHint_1816_, v___y_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1815_ = stack[0].m_obj;
lean_object* v_declHint_1816_ = stack[1].m_obj;
lean_object* v___y_1817_ = stack[2].m_obj;
lean_object* v___y_1818_ = stack[3].m_obj;
lean_object* v___y_1819_ = stack[4].m_obj;
lean_object* v___y_1820_ = stack[5].m_obj;
lean_object* v___y_1821_ = stack[6].m_obj;
lean_object* v___y_1822_ = stack[7].m_obj;
lean_object* v_res_1825_;
v_res_1825_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1815_, v_declHint_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
stack->m_obj
 = v_res_1825_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1826_, lean_object* v_declHint_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1826_, v_declHint_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
return v_res_1835_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1836_, lean_object* v_ref_1837_, lean_object* v_msg_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1837_, v_msg_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1837_ = stack[1].m_obj;
lean_object* v_msg_1838_ = stack[2].m_obj;
lean_object* v___y_1839_ = stack[3].m_obj;
lean_object* v___y_1840_ = stack[4].m_obj;
lean_object* v___y_1841_ = stack[5].m_obj;
lean_object* v___y_1842_ = stack[6].m_obj;
lean_object* v___y_1843_ = stack[7].m_obj;
lean_object* v___y_1844_ = stack[8].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_box(0), v_ref_1837_, v_msg_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_ref_1849_, lean_object* v_msg_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1848_, v_ref_1849_, v_msg_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec(v_ref_1849_);
return v_res_1858_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1859_, lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1860_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1860_ = stack[1].m_obj;
lean_object* v___y_1861_ = stack[2].m_obj;
lean_object* v___y_1862_ = stack[3].m_obj;
lean_object* v___y_1863_ = stack[4].m_obj;
lean_object* v___y_1864_ = stack[5].m_obj;
lean_object* v___y_1865_ = stack[6].m_obj;
lean_object* v___y_1866_ = stack[7].m_obj;
lean_object* v_res_1869_;
v_res_1869_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_box(0), v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
stack->m_obj
 = v_res_1869_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1870_, lean_object* v_msg_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1870_, v_msg_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
return v_res_1879_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1881_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_r_1880_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; 
lean_inc_ref(v_r_1880_);
v___x_1890_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1880_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1943_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1943_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1943_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_expr_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1941_; 
v_expr_1895_ = lean_ctor_get(v_r_1880_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_r_1880_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v_r_1880_, 1);
lean_dec(v_unused_1942_);
v___x_1897_ = v_r_1880_;
v_isShared_1898_ = v_isSharedCheck_1941_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_expr_1895_);
lean_dec(v_r_1880_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1941_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
uint8_t v___x_1899_; 
v___x_1899_ = l_Lean_Expr_isSort(v_a_1891_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; 
lean_del_object(v___x_1893_);
lean_inc(v_a_1886_);
lean_inc_ref(v_a_1885_);
lean_inc(v_a_1884_);
lean_inc_ref(v_a_1883_);
v___x_1900_ = lean_whnf(v_a_1891_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1925_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
if (lean_obj_tag(v_a_1901_) == 3)
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_a_1901_);
lean_inc_ref(v_expr_1895_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1905_);
v___x_1907_ = v___x_1897_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_expr_1895_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v_count_1909_; lean_object* v_results_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1922_; 
v___x_1908_ = lean_st_ref_take(v_a_1882_);
v_count_1909_ = lean_ctor_get(v___x_1908_, 0);
v_results_1910_ = lean_ctor_get(v___x_1908_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1912_ = v___x_1908_;
v_isShared_1913_ = v_isSharedCheck_1922_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_results_1910_);
lean_inc(v_count_1909_);
lean_dec(v___x_1908_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1922_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_inc_ref(v___x_1907_);
v___x_1914_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1910_, v_expr_1895_, v___x_1907_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_count_1909_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1917_ = lean_st_ref_put(v_a_1882_, v___x_1916_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1907_);
v___x_1919_ = v___x_1903_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1907_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
else
{
lean_object* v___x_1924_; 
lean_del_object(v___x_1903_);
lean_dec(v_a_1901_);
lean_del_object(v___x_1897_);
v___x_1924_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1895_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_del_object(v___x_1897_);
lean_dec_ref(v_expr_1895_);
v_a_1926_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1900_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1900_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1891_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1934_);
v___x_1936_ = v___x_1897_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_expr_1895_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1936_);
v___x_1938_ = v___x_1893_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_r_1880_);
v_a_1944_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1890_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1890_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1880_ = stack[0].m_obj;
lean_object* v_a_1881_ = stack[1].m_obj;
lean_object* v_a_1882_ = stack[2].m_obj;
lean_object* v_a_1883_ = stack[3].m_obj;
lean_object* v_a_1884_ = stack[4].m_obj;
lean_object* v_a_1885_ = stack[5].m_obj;
lean_object* v_a_1886_ = stack[6].m_obj;
lean_object* v_res_1952_;
v_res_1952_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
stack->m_obj
 = v_res_1952_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec(v_a_1954_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1962_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = l_Lean_instInhabitedExpr;
v___x_1964_ = lean_panic_fn_borrowed(v___x_1963_, v_msg_1962_);
return v___x_1964_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1969_ = lean_unsigned_to_nat(18u);
v___x_1970_ = lean_unsigned_to_nat(1864u);
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1973_ = l_mkPanicMessageWithDecl(v___x_1972_, v___x_1971_, v___x_1970_, v___x_1969_, v___x_1968_);
return v___x_1973_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1974_, lean_object* v_f_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___y_1985_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1998_; lean_object* v_fType_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; uint8_t v___x_2059_; 
v___x_2059_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1977_);
if (v___x_2059_ == 0)
{
if (lean_obj_tag(v_e_1974_) == 5)
{
lean_object* v_expr_2060_; lean_object* v_expr_2061_; lean_object* v_fn_2062_; lean_object* v_arg_2063_; size_t v___x_2064_; size_t v___x_2065_; uint8_t v___x_2066_; 
v_expr_2060_ = lean_ctor_get(v_f_1975_, 0);
lean_inc_ref(v_expr_2060_);
lean_dec_ref(v_f_1975_);
v_expr_2061_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref(v_expr_2061_);
lean_dec_ref(v_a_1976_);
v_fn_2062_ = lean_ctor_get(v_e_1974_, 0);
v_arg_2063_ = lean_ctor_get(v_e_1974_, 1);
v___x_2064_ = lean_ptr_addr(v_fn_2062_);
v___x_2065_ = lean_ptr_addr(v_expr_2060_);
v___x_2066_ = lean_usize_dec_eq(v___x_2064_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec_ref_known(v_e_1974_, 2);
v___x_2067_ = l_Lean_Expr_app___override(v_expr_2060_, v_expr_2061_);
v___y_1985_ = v___x_2067_;
goto v___jp_1984_;
}
else
{
size_t v___x_2068_; size_t v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = lean_ptr_addr(v_arg_2063_);
v___x_2069_ = lean_ptr_addr(v_expr_2061_);
v___x_2070_ = lean_usize_dec_eq(v___x_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec_ref_known(v_e_1974_, 2);
v___x_2071_ = l_Lean_Expr_app___override(v_expr_2060_, v_expr_2061_);
v___y_1985_ = v___x_2071_;
goto v___jp_1984_;
}
else
{
lean_dec_ref(v_expr_2061_);
lean_dec_ref(v_expr_2060_);
v___y_1985_ = v_e_1974_;
goto v___jp_1984_;
}
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_f_1975_);
lean_dec_ref(v_e_1974_);
v___x_2072_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_2073_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2072_);
v___y_1985_ = v___x_2073_;
goto v___jp_1984_;
}
}
else
{
lean_object* v___x_2074_; 
lean_inc_ref(v_f_1975_);
v___x_2074_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1975_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; uint8_t v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = l_Lean_Expr_isForall(v_a_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
v___x_2077_ = lean_whnf(v_a_2075_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v_fType_2015_ = v_a_2078_;
v___y_2016_ = v_a_1978_;
v___y_2017_ = v_a_1979_;
v___y_2018_ = v_a_1980_;
v___y_2019_ = v_a_1981_;
v___y_2020_ = v_a_1982_;
goto v___jp_2014_;
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_f_1975_);
lean_dec_ref(v_e_1974_);
v_a_2079_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2077_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
v_fType_2015_ = v_a_2075_;
v___y_2016_ = v_a_1978_;
v___y_2017_ = v_a_1979_;
v___y_2018_ = v_a_1980_;
v___y_2019_ = v_a_1981_;
v___y_2020_ = v_a_1982_;
goto v___jp_2014_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_f_1975_);
lean_dec_ref(v_e_1974_);
v_a_2087_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2074_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2074_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
v___jp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___y_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
v___jp_1989_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1993_ = lean_expr_instantiate1(v___y_1990_, v___y_1991_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___y_1990_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___y_1992_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
v___jp_1997_:
{
if (lean_obj_tag(v_e_1974_) == 5)
{
lean_object* v_expr_1999_; lean_object* v_expr_2000_; lean_object* v_fn_2001_; lean_object* v_arg_2002_; size_t v___x_2003_; size_t v___x_2004_; uint8_t v___x_2005_; 
v_expr_1999_ = lean_ctor_get(v_f_1975_, 0);
lean_inc_ref(v_expr_1999_);
lean_dec_ref(v_f_1975_);
v_expr_2000_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref(v_expr_2000_);
lean_dec_ref(v_a_1976_);
v_fn_2001_ = lean_ctor_get(v_e_1974_, 0);
v_arg_2002_ = lean_ctor_get(v_e_1974_, 1);
v___x_2003_ = lean_ptr_addr(v_fn_2001_);
v___x_2004_ = lean_ptr_addr(v_expr_1999_);
v___x_2005_ = lean_usize_dec_eq(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec_ref_known(v_e_1974_, 2);
lean_inc_ref(v_expr_2000_);
v___x_2006_ = l_Lean_Expr_app___override(v_expr_1999_, v_expr_2000_);
v___y_1990_ = v___y_1998_;
v___y_1991_ = v_expr_2000_;
v___y_1992_ = v___x_2006_;
goto v___jp_1989_;
}
else
{
size_t v___x_2007_; size_t v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = lean_ptr_addr(v_arg_2002_);
v___x_2008_ = lean_ptr_addr(v_expr_2000_);
v___x_2009_ = lean_usize_dec_eq(v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref_known(v_e_1974_, 2);
lean_inc_ref(v_expr_2000_);
v___x_2010_ = l_Lean_Expr_app___override(v_expr_1999_, v_expr_2000_);
v___y_1990_ = v___y_1998_;
v___y_1991_ = v_expr_2000_;
v___y_1992_ = v___x_2010_;
goto v___jp_1989_;
}
else
{
lean_dec_ref(v_expr_1999_);
v___y_1990_ = v___y_1998_;
v___y_1991_ = v_expr_2000_;
v___y_1992_ = v_e_1974_;
goto v___jp_1989_;
}
}
}
else
{
lean_object* v_expr_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec_ref(v_f_1975_);
lean_dec_ref(v_e_1974_);
v_expr_2011_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref(v_expr_2011_);
lean_dec_ref(v_a_1976_);
v___x_2012_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_2013_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2012_);
v___y_1990_ = v___y_1998_;
v___y_1991_ = v_expr_2011_;
v___y_1992_ = v___x_2013_;
goto v___jp_1989_;
}
}
v___jp_2014_:
{
if (lean_obj_tag(v_fType_2015_) == 7)
{
lean_object* v_binderType_2021_; lean_object* v_body_2022_; lean_object* v___x_2023_; 
v_binderType_2021_ = lean_ctor_get(v_fType_2015_, 1);
lean_inc_ref(v_binderType_2021_);
v_body_2022_ = lean_ctor_get(v_fType_2015_, 2);
lean_inc_ref(v_body_2022_);
lean_dec_ref_known(v_fType_2015_, 3);
lean_inc_ref(v_a_1976_);
v___x_2023_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1976_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = l_Lean_Meta_isExprDefEq(v_binderType_2021_, v_a_2024_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; uint8_t v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = lean_unbox(v_a_2026_);
lean_dec(v_a_2026_);
if (v___x_2027_ == 0)
{
lean_object* v_expr_2028_; lean_object* v_expr_2029_; lean_object* v___x_2030_; 
v_expr_2028_ = lean_ctor_get(v_f_1975_, 0);
v_expr_2029_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref(v_expr_2029_);
lean_inc_ref(v_expr_2028_);
v___x_2030_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_2028_, v_expr_2029_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_dec_ref_known(v___x_2030_, 1);
v___y_1998_ = v_body_2022_;
goto v___jp_1997_;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_body_2022_);
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_f_1975_);
lean_dec_ref(v_e_1974_);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
v___y_1998_ = v_body_2022_;
goto v___jp_1997_;
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_body_2022_);
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_f_1975_);
lean_dec_ref(v_e_1974_);
v_a_2039_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2025_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2025_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v_body_2022_);
lean_dec_ref(v_binderType_2021_);
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_f_1975_);
lean_dec_ref(v_e_1974_);
v_a_2047_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2023_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2023_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_expr_2055_; lean_object* v_expr_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec_ref(v_fType_2015_);
lean_dec_ref(v_e_1974_);
v_expr_2055_ = lean_ctor_get(v_f_1975_, 0);
lean_inc_ref(v_expr_2055_);
lean_dec_ref(v_f_1975_);
v_expr_2056_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref(v_expr_2056_);
lean_dec_ref(v_a_1976_);
v___x_2057_ = l_Lean_Expr_app___override(v_expr_2055_, v_expr_2056_);
v___x_2058_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_2057_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1974_ = stack[0].m_obj;
lean_object* v_f_1975_ = stack[1].m_obj;
lean_object* v_a_1976_ = stack[2].m_obj;
lean_object* v_a_1977_ = stack[3].m_obj;
lean_object* v_a_1978_ = stack[4].m_obj;
lean_object* v_a_1979_ = stack[5].m_obj;
lean_object* v_a_1980_ = stack[6].m_obj;
lean_object* v_a_1981_ = stack[7].m_obj;
lean_object* v_a_1982_ = stack[8].m_obj;
lean_object* v_res_2095_;
v_res_2095_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_1974_, v_f_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
stack->m_obj
 = v_res_2095_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2096_, lean_object* v_f_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2096_, v_f_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec(v_a_2099_);
return v_res_2106_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2108_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2109_ = lean_unsigned_to_nat(37u);
v___x_2110_ = lean_unsigned_to_nat(345u);
v___x_2111_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2113_ = l_mkPanicMessageWithDecl(v___x_2112_, v___x_2111_, v___x_2110_, v___x_2109_, v___x_2108_);
return v___x_2113_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2114_, lean_object* v_i_2115_, lean_object* v_a_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_zero_2124_; uint8_t v_isZero_2125_; 
v_zero_2124_ = lean_unsigned_to_nat(0u);
v_isZero_2125_ = lean_nat_dec_eq(v_i_2115_, v_zero_2124_);
if (v_isZero_2125_ == 1)
{
lean_object* v___x_2126_; 
lean_dec(v_i_2115_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2116_);
return v___x_2126_;
}
else
{
lean_object* v_one_2127_; lean_object* v_n_2128_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2139_; lean_object* v___x_2142_; 
v_one_2127_ = lean_unsigned_to_nat(1u);
v_n_2128_ = lean_nat_sub(v_i_2115_, v_one_2127_);
lean_dec(v_i_2115_);
v___x_2142_ = lean_array_fget_borrowed(v_fvars_2114_, v_n_2128_);
if (lean_obj_tag(v___x_2142_) == 1)
{
lean_object* v_fvarId_2143_; lean_object* v___x_2144_; 
v_fvarId_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_fvarId_2143_);
v___x_2144_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2143_, v___y_2119_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
if (lean_obj_tag(v_a_2145_) == 1)
{
lean_object* v_val_2146_; 
v_val_2146_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_val_2146_);
lean_dec_ref_known(v_a_2145_, 1);
if (lean_obj_tag(v_val_2146_) == 0)
{
lean_object* v_userName_2147_; lean_object* v_type_2148_; uint8_t v_bi_2149_; lean_object* v_expr_2150_; lean_object* v_type_x3f_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2172_; 
v_userName_2147_ = lean_ctor_get(v_val_2146_, 2);
lean_inc(v_userName_2147_);
v_type_2148_ = lean_ctor_get(v_val_2146_, 3);
lean_inc_ref(v_type_2148_);
v_bi_2149_ = lean_ctor_get_uint8(v_val_2146_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2146_, 4);
v_expr_2150_ = lean_ctor_get(v_a_2116_, 0);
v_type_x3f_2151_ = lean_ctor_get(v_a_2116_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2153_ = v_a_2116_;
v_isShared_2154_ = v_isSharedCheck_2172_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_type_x3f_2151_);
lean_inc(v_expr_2150_);
lean_dec(v_a_2116_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2172_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___y_2158_; 
v___x_2155_ = lean_expr_abstract_range(v_type_2148_, v_n_2128_, v_fvars_2114_);
lean_dec_ref(v_type_2148_);
lean_inc_ref(v___x_2155_);
lean_inc(v_userName_2147_);
v___x_2156_ = l_Lean_Expr_lam___override(v_userName_2147_, v___x_2155_, v_expr_2150_, v_bi_2149_);
if (lean_obj_tag(v_type_x3f_2151_) == 0)
{
lean_dec_ref(v___x_2155_);
lean_dec(v_userName_2147_);
v___y_2158_ = v_type_x3f_2151_;
goto v___jp_2157_;
}
else
{
lean_object* v_val_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2171_; 
v_val_2163_ = lean_ctor_get(v_type_x3f_2151_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_type_x3f_2151_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2165_ = v_type_x3f_2151_;
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_val_2163_);
lean_dec(v_type_x3f_2151_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = l_Lean_Expr_forallE___override(v_userName_2147_, v___x_2155_, v_val_2163_, v_bi_2149_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2167_);
v___x_2169_ = v___x_2165_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
v___y_2158_ = v___x_2169_;
goto v___jp_2157_;
}
}
}
v___jp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___y_2158_);
lean_ctor_set(v___x_2153_, 0, v___x_2156_);
v___x_2160_ = v___x_2153_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___y_2158_);
v___x_2160_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
v_i_2115_ = v_n_2128_;
v_a_2116_ = v___x_2160_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2173_; lean_object* v_type_2174_; lean_object* v_value_2175_; uint8_t v_nondep_2176_; uint8_t v_nondep_2178_; lean_object* v___x_2188_; 
v_userName_2173_ = lean_ctor_get(v_val_2146_, 2);
lean_inc(v_userName_2173_);
v_type_2174_ = lean_ctor_get(v_val_2146_, 3);
lean_inc_ref(v_type_2174_);
v_value_2175_ = lean_ctor_get(v_val_2146_, 4);
lean_inc_ref(v_value_2175_);
v_nondep_2176_ = lean_ctor_get_uint8(v_val_2146_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2146_, 5);
v___x_2188_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2120_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; uint8_t v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = 1;
if (v_nondep_2176_ == 0)
{
uint8_t v___x_2191_; 
v___x_2191_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2143_, v_a_2189_);
lean_dec(v_a_2189_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
v___x_2192_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2118_);
lean_dec_ref(v___x_2192_);
v_nondep_2178_ = v___x_2190_;
goto v___jp_2177_;
}
else
{
v_nondep_2178_ = v_nondep_2176_;
goto v___jp_2177_;
}
}
else
{
lean_dec(v_a_2189_);
v_nondep_2178_ = v___x_2190_;
goto v___jp_2177_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v_value_2175_);
lean_dec_ref(v_type_2174_);
lean_dec(v_userName_2173_);
lean_dec(v_n_2128_);
lean_dec_ref(v_a_2116_);
v_a_2193_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2188_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2188_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
v___jp_2177_:
{
lean_object* v_expr_2179_; lean_object* v_type_x3f_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_expr_2179_ = lean_ctor_get(v_a_2116_, 0);
lean_inc_ref(v_expr_2179_);
v_type_x3f_2180_ = lean_ctor_get(v_a_2116_, 1);
lean_inc(v_type_x3f_2180_);
lean_dec_ref(v_a_2116_);
v___x_2181_ = lean_expr_abstract_range(v_type_2174_, v_n_2128_, v_fvars_2114_);
lean_dec_ref(v_type_2174_);
v___x_2182_ = lean_expr_abstract_range(v_value_2175_, v_n_2128_, v_fvars_2114_);
lean_dec_ref(v_value_2175_);
lean_inc_ref(v___x_2182_);
lean_inc_ref(v___x_2181_);
lean_inc(v_userName_2173_);
v___x_2183_ = l_Lean_Expr_letE___override(v_userName_2173_, v___x_2181_, v___x_2182_, v_expr_2179_, v_nondep_2178_);
if (lean_obj_tag(v_type_x3f_2180_) == 0)
{
lean_dec_ref(v___x_2182_);
lean_dec_ref(v___x_2181_);
lean_dec(v_userName_2173_);
v___y_2130_ = v___x_2183_;
v___y_2131_ = v_type_x3f_2180_;
goto v___jp_2129_;
}
else
{
lean_object* v_val_2184_; uint8_t v___x_2185_; 
v_val_2184_ = lean_ctor_get(v_type_x3f_2180_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v_type_x3f_2180_, 1);
v___x_2185_ = lean_expr_has_loose_bvar(v_val_2184_, v_zero_2124_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_dec_ref(v___x_2182_);
lean_dec_ref(v___x_2181_);
lean_dec(v_userName_2173_);
v___x_2186_ = lean_expr_lower_loose_bvars(v_val_2184_, v_one_2127_, v_one_2127_);
lean_dec(v_val_2184_);
v___y_2135_ = v___x_2183_;
v___y_2136_ = v___x_2186_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_Expr_letE___override(v_userName_2173_, v___x_2181_, v___x_2182_, v_val_2184_, v_nondep_2178_);
v___y_2135_ = v___x_2183_;
v___y_2136_ = v___x_2187_;
goto v___jp_2134_;
}
}
}
}
}
else
{
lean_object* v___x_2201_; 
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2116_);
lean_inc(v_fvarId_2143_);
v___x_2201_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2143_, v___y_2121_, v___y_2122_);
v___y_2139_ = v___x_2201_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_n_2128_);
lean_dec_ref(v_a_2116_);
v_a_2202_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2144_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2144_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v_a_2116_);
v___x_2210_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2211_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2210_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
v___y_2139_ = v___x_2211_;
goto v___jp_2138_;
}
v___jp_2129_:
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___y_2130_);
lean_ctor_set(v___x_2132_, 1, v___y_2131_);
v_i_2115_ = v_n_2128_;
v_a_2116_ = v___x_2132_;
goto _start;
}
v___jp_2134_:
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___y_2136_);
v___y_2130_ = v___y_2135_;
v___y_2131_ = v___x_2137_;
goto v___jp_2129_;
}
v___jp_2138_:
{
if (lean_obj_tag(v___y_2139_) == 0)
{
lean_object* v_a_2140_; 
v_a_2140_ = lean_ctor_get(v___y_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___y_2139_, 1);
v_i_2115_ = v_n_2128_;
v_a_2116_ = v_a_2140_;
goto _start;
}
else
{
lean_dec(v_n_2128_);
return v___y_2139_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2114_ = stack[0].m_obj;
lean_object* v_i_2115_ = stack[1].m_obj;
lean_object* v_a_2116_ = stack[2].m_obj;
lean_object* v___y_2117_ = stack[3].m_obj;
lean_object* v___y_2118_ = stack[4].m_obj;
lean_object* v___y_2119_ = stack[5].m_obj;
lean_object* v___y_2120_ = stack[6].m_obj;
lean_object* v___y_2121_ = stack[7].m_obj;
lean_object* v___y_2122_ = stack[8].m_obj;
lean_object* v_res_2212_;
v_res_2212_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2114_, v_i_2115_, v_a_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
stack->m_obj
 = v_res_2212_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2213_, lean_object* v_i_2214_, lean_object* v_a_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2213_, v_i_2214_, v_a_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v_fvars_2213_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
if (lean_obj_tag(v_a_2224_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = l_List_reverse___redArg(v_a_2225_);
return v___x_2226_;
}
else
{
lean_object* v_head_2227_; lean_object* v_tail_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2237_; 
v_head_2227_ = lean_ctor_get(v_a_2224_, 0);
v_tail_2228_ = lean_ctor_get(v_a_2224_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_a_2224_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2230_ = v_a_2224_;
v_isShared_2231_ = v_isSharedCheck_2237_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_tail_2228_);
lean_inc(v_head_2227_);
lean_dec(v_a_2224_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2237_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = l_Lean_MessageData_ofExpr(v_head_2227_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v_a_2225_);
lean_ctor_set(v___x_2230_, 0, v___x_2232_);
v___x_2234_ = v___x_2230_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_a_2225_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v_a_2224_ = v_tail_2228_;
v_a_2225_ = v___x_2234_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2238_; double v___x_2239_; 
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_float_of_nat(v___x_2238_);
return v___x_2239_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2243_, lean_object* v_msg_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_ref_2250_; lean_object* v___x_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2297_; 
v_ref_2250_ = lean_ctor_get(v___y_2247_, 2);
v___x_2251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2297_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2297_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v_traceState_2257_; lean_object* v_env_2258_; lean_object* v_nextMacroScope_2259_; lean_object* v_ngen_2260_; lean_object* v_auxDeclNGen_2261_; lean_object* v_cache_2262_; lean_object* v_recordedDeps_2263_; lean_object* v_messages_2264_; lean_object* v_infoState_2265_; lean_object* v_snapshotTasks_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2296_; 
v___x_2256_ = lean_st_ref_take(v___y_2248_);
v_traceState_2257_ = lean_ctor_get(v___x_2256_, 4);
v_env_2258_ = lean_ctor_get(v___x_2256_, 0);
v_nextMacroScope_2259_ = lean_ctor_get(v___x_2256_, 1);
v_ngen_2260_ = lean_ctor_get(v___x_2256_, 2);
v_auxDeclNGen_2261_ = lean_ctor_get(v___x_2256_, 3);
v_cache_2262_ = lean_ctor_get(v___x_2256_, 5);
v_recordedDeps_2263_ = lean_ctor_get(v___x_2256_, 6);
v_messages_2264_ = lean_ctor_get(v___x_2256_, 7);
v_infoState_2265_ = lean_ctor_get(v___x_2256_, 8);
v_snapshotTasks_2266_ = lean_ctor_get(v___x_2256_, 9);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2268_ = v___x_2256_;
v_isShared_2269_ = v_isSharedCheck_2296_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_snapshotTasks_2266_);
lean_inc(v_infoState_2265_);
lean_inc(v_messages_2264_);
lean_inc(v_recordedDeps_2263_);
lean_inc(v_cache_2262_);
lean_inc(v_traceState_2257_);
lean_inc(v_auxDeclNGen_2261_);
lean_inc(v_ngen_2260_);
lean_inc(v_nextMacroScope_2259_);
lean_inc(v_env_2258_);
lean_dec(v___x_2256_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2296_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint64_t v_tid_2270_; lean_object* v_traces_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2295_; 
v_tid_2270_ = lean_ctor_get_uint64(v_traceState_2257_, sizeof(void*)*1);
v_traces_2271_ = lean_ctor_get(v_traceState_2257_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_traceState_2257_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2273_ = v_traceState_2257_;
v_isShared_2274_ = v_isSharedCheck_2295_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_traces_2271_);
lean_dec(v_traceState_2257_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2295_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; double v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2278_ = 0;
v___x_2279_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2280_, 0, v_cls_2243_);
lean_ctor_set(v___x_2280_, 1, v___x_2276_);
lean_ctor_set(v___x_2280_, 2, v___x_2279_);
lean_ctor_set_float(v___x_2280_, sizeof(void*)*3, v___x_2277_);
lean_ctor_set_float(v___x_2280_, sizeof(void*)*3 + 8, v___x_2277_);
lean_ctor_set_uint8(v___x_2280_, sizeof(void*)*3 + 16, v___x_2278_);
v___x_2281_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v_a_2252_);
lean_ctor_set(v___x_2282_, 2, v___x_2281_);
lean_inc(v_ref_2250_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v_ref_2250_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_PersistentArray_push___redArg(v_traces_2271_, v___x_2283_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2284_);
v___x_2286_ = v___x_2273_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2284_);
lean_ctor_set_uint64(v_reuseFailAlloc_2294_, sizeof(void*)*1, v_tid_2270_);
v___x_2286_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v___x_2286_);
v___x_2288_ = v___x_2268_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_env_2258_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_nextMacroScope_2259_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_ngen_2260_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_auxDeclNGen_2261_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2293_, 5, v_cache_2262_);
lean_ctor_set(v_reuseFailAlloc_2293_, 6, v_recordedDeps_2263_);
lean_ctor_set(v_reuseFailAlloc_2293_, 7, v_messages_2264_);
lean_ctor_set(v_reuseFailAlloc_2293_, 8, v_infoState_2265_);
lean_ctor_set(v_reuseFailAlloc_2293_, 9, v_snapshotTasks_2266_);
v___x_2288_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2289_ = lean_st_ref_put(v___y_2248_, v___x_2288_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2275_);
v___x_2291_ = v___x_2254_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2275_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2243_ = stack[0].m_obj;
lean_object* v_msg_2244_ = stack[1].m_obj;
lean_object* v___y_2245_ = stack[2].m_obj;
lean_object* v___y_2246_ = stack[3].m_obj;
lean_object* v___y_2247_ = stack[4].m_obj;
lean_object* v___y_2248_ = stack[5].m_obj;
lean_object* v_res_2298_;
v_res_2298_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2243_, v_msg_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
stack->m_obj
 = v_res_2298_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2299_, lean_object* v_msg_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2299_, v_msg_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
return v_res_2306_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_cls_2317_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2318_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2319_ = l_Lean_Name_append(v___x_2318_, v_cls_2317_);
return v___x_2319_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2328_ = l_Lean_stringToMessageData(v___x_2327_);
return v___x_2328_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2333_ = l_Lean_MessageData_ofFormat(v___x_2332_);
return v___x_2333_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2334_, lean_object* v_body_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v_toCold_2374_; lean_object* v_options_2375_; uint8_t v_hasTrace_2376_; 
v_toCold_2374_ = lean_ctor_get(v_a_2340_, 0);
v_options_2375_ = lean_ctor_get(v_toCold_2374_, 2);
v_hasTrace_2376_ = lean_ctor_get_uint8(v_options_2375_, sizeof(void*)*1);
if (v_hasTrace_2376_ == 0)
{
v___y_2356_ = v_a_2336_;
v___y_2357_ = v_a_2337_;
v___y_2358_ = v_a_2338_;
v___y_2359_ = v_a_2339_;
v___y_2360_ = v_a_2340_;
v___y_2361_ = v_a_2341_;
goto v___jp_2355_;
}
else
{
lean_object* v_inheritedTraceOptions_2377_; lean_object* v_cls_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_inheritedTraceOptions_2377_ = lean_ctor_get(v_toCold_2374_, 11);
v_cls_2378_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2379_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2377_, v_options_2375_, v___x_2379_);
if (v___x_2380_ == 0)
{
v___y_2356_ = v_a_2336_;
v___y_2357_ = v_a_2337_;
v___y_2358_ = v_a_2338_;
v___y_2359_ = v_a_2339_;
v___y_2360_ = v_a_2340_;
v___y_2361_ = v_a_2341_;
goto v___jp_2355_;
}
else
{
lean_object* v_expr_2381_; lean_object* v_type_x3f_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___y_2395_; 
v_expr_2381_ = lean_ctor_get(v_body_2335_, 0);
v_type_x3f_2382_ = lean_ctor_get(v_body_2335_, 1);
v___x_2383_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2334_);
v___x_2384_ = lean_array_to_list(v_fvars_2334_);
v___x_2385_ = lean_box(0);
v___x_2386_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2384_, v___x_2385_);
v___x_2387_ = l_Lean_MessageData_ofList(v___x_2386_);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2383_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
lean_inc_ref(v_expr_2381_);
v___x_2391_ = l_Lean_MessageData_ofExpr(v_expr_2381_);
v___x_2392_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
if (lean_obj_tag(v_type_x3f_2382_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2395_ = v___x_2408_;
goto v___jp_2394_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2410_; 
v_val_2409_ = lean_ctor_get(v_type_x3f_2382_, 0);
lean_inc(v_val_2409_);
v___x_2410_ = l_Lean_MessageData_ofExpr(v_val_2409_);
v___y_2395_ = v___x_2410_;
goto v___jp_2394_;
}
v___jp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2393_);
lean_ctor_set(v___x_2396_, 1, v___y_2395_);
v___x_2397_ = l_Lean_indentD(v___x_2396_);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2390_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2378_, v___x_2398_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_dec_ref_known(v___x_2399_, 1);
v___y_2356_ = v_a_2336_;
v___y_2357_ = v_a_2337_;
v___y_2358_ = v_a_2338_;
v___y_2359_ = v_a_2339_;
v___y_2360_ = v_a_2340_;
v___y_2361_ = v_a_2341_;
goto v___jp_2355_;
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec_ref(v_body_2335_);
lean_dec_ref(v_fvars_2334_);
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
v___jp_2343_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2347_);
lean_ctor_set(v___x_2352_, 1, v___y_2351_);
v___x_2353_ = lean_array_get_size(v_fvars_2334_);
v___x_2354_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2334_, v___x_2353_, v___x_2352_, v___y_2350_, v___y_2349_, v___y_2345_, v___y_2344_, v___y_2346_, v___y_2348_);
lean_dec_ref(v_fvars_2334_);
return v___x_2354_;
}
v___jp_2355_:
{
lean_object* v_expr_2362_; lean_object* v_type_x3f_2363_; lean_object* v___x_2364_; 
v_expr_2362_ = lean_ctor_get(v_body_2335_, 0);
lean_inc_ref(v_expr_2362_);
v_type_x3f_2363_ = lean_ctor_get(v_body_2335_, 1);
lean_inc(v_type_x3f_2363_);
lean_dec_ref(v_body_2335_);
v___x_2364_ = lean_expr_abstract(v_expr_2362_, v_fvars_2334_);
lean_dec_ref(v_expr_2362_);
if (lean_obj_tag(v_type_x3f_2363_) == 0)
{
v___y_2344_ = v___y_2359_;
v___y_2345_ = v___y_2358_;
v___y_2346_ = v___y_2360_;
v___y_2347_ = v___x_2364_;
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2357_;
v___y_2350_ = v___y_2356_;
v___y_2351_ = v_type_x3f_2363_;
goto v___jp_2343_;
}
else
{
lean_object* v_val_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2373_; 
v_val_2365_ = lean_ctor_get(v_type_x3f_2363_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_type_x3f_2363_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2367_ = v_type_x3f_2363_;
v_isShared_2368_ = v_isSharedCheck_2373_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_val_2365_);
lean_dec(v_type_x3f_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2373_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_expr_abstract(v_val_2365_, v_fvars_2334_);
lean_dec(v_val_2365_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2369_);
v___x_2371_ = v___x_2367_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
v___y_2344_ = v___y_2359_;
v___y_2345_ = v___y_2358_;
v___y_2346_ = v___y_2360_;
v___y_2347_ = v___x_2364_;
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2357_;
v___y_2350_ = v___y_2356_;
v___y_2351_ = v___x_2371_;
goto v___jp_2343_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2334_ = stack[0].m_obj;
lean_object* v_body_2335_ = stack[1].m_obj;
lean_object* v_a_2336_ = stack[2].m_obj;
lean_object* v_a_2337_ = stack[3].m_obj;
lean_object* v_a_2338_ = stack[4].m_obj;
lean_object* v_a_2339_ = stack[5].m_obj;
lean_object* v_a_2340_ = stack[6].m_obj;
lean_object* v_a_2341_ = stack[7].m_obj;
lean_object* v_res_2411_;
v_res_2411_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2334_, v_body_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
stack->m_obj
 = v_res_2411_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2412_, lean_object* v_body_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2412_, v_body_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec(v_a_2414_);
return v_res_2421_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2422_, lean_object* v_n_2423_, lean_object* v_i_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2422_, v_i_2424_, v_a_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2422_ = stack[0].m_obj;
lean_object* v_n_2423_ = stack[1].m_obj;
lean_object* v_i_2424_ = stack[2].m_obj;
lean_object* v_a_2426_ = stack[4].m_obj;
lean_object* v___y_2427_ = stack[5].m_obj;
lean_object* v___y_2428_ = stack[6].m_obj;
lean_object* v___y_2429_ = stack[7].m_obj;
lean_object* v___y_2430_ = stack[8].m_obj;
lean_object* v___y_2431_ = stack[9].m_obj;
lean_object* v___y_2432_ = stack[10].m_obj;
lean_object* v_res_2435_;
v_res_2435_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2422_, v_n_2423_, v_i_2424_, lean_box(0), v_a_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
stack->m_obj
 = v_res_2435_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2436_, lean_object* v_n_2437_, lean_object* v_i_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2436_, v_n_2437_, v_i_2438_, v_a_2439_, v_a_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec(v_n_2437_);
lean_dec_ref(v_fvars_2436_);
return v_res_2448_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2449_, lean_object* v_msg_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2449_, v_msg_2450_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2449_ = stack[0].m_obj;
lean_object* v_msg_2450_ = stack[1].m_obj;
lean_object* v___y_2451_ = stack[2].m_obj;
lean_object* v___y_2452_ = stack[3].m_obj;
lean_object* v___y_2453_ = stack[4].m_obj;
lean_object* v___y_2454_ = stack[5].m_obj;
lean_object* v___y_2455_ = stack[6].m_obj;
lean_object* v___y_2456_ = stack[7].m_obj;
lean_object* v_res_2459_;
v_res_2459_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2449_, v_msg_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
stack->m_obj
 = v_res_2459_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2460_, lean_object* v_msg_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2460_, v_msg_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
return v_res_2469_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2472_ = l_Lean_stringToMessageData(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2475_ = l_Lean_stringToMessageData(v___x_2474_);
return v___x_2475_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2476_, lean_object* v_structName_2477_, lean_object* v_idx_2478_, lean_object* v_a_2479_, lean_object* v_00_u03b1_2480_, lean_object* v_x_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_expr_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2504_; 
v_expr_2489_ = lean_ctor_get(v_struct_2476_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_struct_2476_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v_struct_2476_, 1);
lean_dec(v_unused_2505_);
v___x_2491_ = v_struct_2476_;
v_isShared_2492_ = v_isSharedCheck_2504_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_expr_2489_);
lean_dec(v_struct_2476_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2504_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2493_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2494_ = l_Lean_mkProj(v_structName_2477_, v_idx_2478_, v_expr_2489_);
v___x_2495_ = l_Lean_indentExpr(v___x_2494_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 7);
lean_ctor_set(v___x_2491_, 1, v___x_2495_);
lean_ctor_set(v___x_2491_, 0, v___x_2493_);
v___x_2497_ = v___x_2491_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2498_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = l_Lean_indentExpr(v_a_2479_);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2501_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
return v___x_2502_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_struct_2476_ = stack[0].m_obj;
lean_object* v_structName_2477_ = stack[1].m_obj;
lean_object* v_idx_2478_ = stack[2].m_obj;
lean_object* v_a_2479_ = stack[3].m_obj;
lean_object* v_x_2481_ = stack[5].m_obj;
lean_object* v___y_2482_ = stack[6].m_obj;
lean_object* v___y_2483_ = stack[7].m_obj;
lean_object* v___y_2484_ = stack[8].m_obj;
lean_object* v___y_2485_ = stack[9].m_obj;
lean_object* v___y_2486_ = stack[10].m_obj;
lean_object* v___y_2487_ = stack[11].m_obj;
lean_object* v_res_2506_;
v_res_2506_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2476_, v_structName_2477_, v_idx_2478_, v_a_2479_, lean_box(0), v_x_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
stack->m_obj
 = v_res_2506_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2507_, lean_object* v_structName_2508_, lean_object* v_idx_2509_, lean_object* v_a_2510_, lean_object* v_00_u03b1_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2507_, v_structName_2508_, v_idx_2509_, v_a_2510_, v_00_u03b1_2511_, v_x_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
return v_res_2520_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v_env_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2529_ = lean_st_ref_get(v___y_2527_);
v_env_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_ref(v_env_2530_);
lean_dec(v___x_2529_);
v___x_2531_ = 0;
lean_inc(v_constName_2521_);
v___x_2532_ = l_Lean_Environment_find_x3f(v_env_2530_, v_constName_2521_, v___x_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v___x_2533_;
}
else
{
lean_object* v_val_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_constName_2521_);
v_val_2534_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2532_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_val_2534_);
lean_dec(v___x_2532_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 0);
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_val_2534_);
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
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2521_ = stack[0].m_obj;
lean_object* v___y_2522_ = stack[1].m_obj;
lean_object* v___y_2523_ = stack[2].m_obj;
lean_object* v___y_2524_ = stack[3].m_obj;
lean_object* v___y_2525_ = stack[4].m_obj;
lean_object* v___y_2526_ = stack[5].m_obj;
lean_object* v___y_2527_ = stack[6].m_obj;
lean_object* v_res_2542_;
v_res_2542_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
stack->m_obj
 = v_res_2542_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec(v___y_2544_);
return v_res_2551_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2552_, lean_object* v_structName_2553_, lean_object* v_idx_2554_, lean_object* v_a_2555_, lean_object* v_00_u03b1_2556_, lean_object* v_x_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_expr_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2580_; 
v_expr_2565_ = lean_ctor_get(v_struct_2552_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_struct_2552_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v_struct_2552_, 1);
lean_dec(v_unused_2581_);
v___x_2567_ = v_struct_2552_;
v_isShared_2568_ = v_isSharedCheck_2580_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_expr_2565_);
lean_dec(v_struct_2552_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2580_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2569_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2570_ = l_Lean_mkProj(v_structName_2553_, v_idx_2554_, v_expr_2565_);
v___x_2571_ = l_Lean_indentExpr(v___x_2570_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 7);
lean_ctor_set(v___x_2567_, 1, v___x_2571_);
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2573_ = v___x_2567_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2574_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l_Lean_indentExpr(v_a_2555_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2577_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_struct_2552_ = stack[0].m_obj;
lean_object* v_structName_2553_ = stack[1].m_obj;
lean_object* v_idx_2554_ = stack[2].m_obj;
lean_object* v_a_2555_ = stack[3].m_obj;
lean_object* v_x_2557_ = stack[5].m_obj;
lean_object* v___y_2558_ = stack[6].m_obj;
lean_object* v___y_2559_ = stack[7].m_obj;
lean_object* v___y_2560_ = stack[8].m_obj;
lean_object* v___y_2561_ = stack[9].m_obj;
lean_object* v___y_2562_ = stack[10].m_obj;
lean_object* v___y_2563_ = stack[11].m_obj;
lean_object* v_res_2582_;
v_res_2582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2552_, v_structName_2553_, v_idx_2554_, v_a_2555_, lean_box(0), v_x_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
stack->m_obj
 = v_res_2582_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2583_, lean_object* v_structName_2584_, lean_object* v_idx_2585_, lean_object* v_a_2586_, lean_object* v_00_u03b1_2587_, lean_object* v_x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2583_, v_structName_2584_, v_idx_2585_, v_a_2586_, v_00_u03b1_2587_, v_x_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec(v___y_2589_);
return v_res_2596_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2597_, lean_object* v_fst_2598_, lean_object* v_struct_2599_, lean_object* v_structName_2600_, uint8_t v_a_2601_, lean_object* v___f_2602_, lean_object* v_snd_2603_, lean_object* v_____r_2604_, lean_object* v_ctorType_2605_, lean_object* v_j_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
if (lean_obj_tag(v_ctorType_2605_) == 7)
{
lean_object* v_binderType_2614_; lean_object* v_body_2615_; lean_object* v___x_2616_; 
lean_dec(v_snd_2603_);
v_binderType_2614_ = lean_ctor_get(v_ctorType_2605_, 1);
lean_inc_ref(v_binderType_2614_);
v_body_2615_ = lean_ctor_get(v_ctorType_2605_, 2);
lean_inc_ref(v_body_2615_);
lean_dec_ref_known(v_ctorType_2605_, 3);
v___x_2616_ = lean_expr_instantiate_rev_range(v_binderType_2614_, v_j_2606_, v_a_2597_, v_fst_2598_);
lean_dec_ref(v_binderType_2614_);
if (v_a_2601_ == 0)
{
lean_dec_ref(v___f_2602_);
goto v___jp_2617_;
}
else
{
lean_object* v___x_2633_; 
lean_inc_ref(v___x_2616_);
v___x_2633_ = l_Lean_Meta_isProp(v___x_2616_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; uint8_t v___x_2635_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = lean_unbox(v_a_2634_);
lean_dec(v_a_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_box(0);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
lean_inc(v___y_2610_);
lean_inc_ref(v___y_2609_);
lean_inc(v___y_2608_);
lean_inc(v___y_2607_);
v___x_2637_ = lean_apply_9(v___f_2602_, lean_box(0), v___x_2636_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_dec_ref_known(v___x_2637_, 1);
goto v___jp_2617_;
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v___x_2616_);
lean_dec_ref(v_body_2615_);
lean_dec(v_structName_2600_);
lean_dec_ref(v_struct_2599_);
lean_dec(v_fst_2598_);
lean_dec(v_a_2597_);
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_dec_ref(v___f_2602_);
goto v___jp_2617_;
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v___x_2616_);
lean_dec_ref(v_body_2615_);
lean_dec_ref(v___f_2602_);
lean_dec(v_structName_2600_);
lean_dec_ref(v_struct_2599_);
lean_dec(v_fst_2598_);
lean_dec(v_a_2597_);
v_a_2646_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2633_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2633_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
v___jp_2617_:
{
lean_object* v_expr_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2631_; 
v_expr_2618_ = lean_ctor_get(v_struct_2599_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_struct_2599_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v_struct_2599_, 1);
lean_dec(v_unused_2632_);
v___x_2620_ = v_struct_2599_;
v_isShared_2621_ = v_isSharedCheck_2631_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_expr_2618_);
lean_dec(v_struct_2599_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2631_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = l_Lean_Expr_proj___override(v_structName_2600_, v_a_2597_, v_expr_2618_);
v___x_2623_ = lean_array_push(v_fst_2598_, v___x_2622_);
lean_inc(v_j_2606_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v___x_2616_);
lean_ctor_set(v___x_2620_, 0, v_j_2606_);
v___x_2625_ = v___x_2620_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_j_2606_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v___x_2616_);
v___x_2625_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2623_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_body_2615_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
return v___x_2629_;
}
}
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec(v_structName_2600_);
lean_dec_ref(v_struct_2599_);
lean_dec(v_a_2597_);
v___x_2654_ = lean_box(0);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
lean_inc(v___y_2610_);
lean_inc_ref(v___y_2609_);
lean_inc(v___y_2608_);
lean_inc(v___y_2607_);
v___x_2655_ = lean_apply_9(v___f_2602_, lean_box(0), v___x_2654_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2655_, 0);
lean_dec(v_unused_2667_);
v___x_2657_ = v___x_2655_;
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
else
{
lean_dec(v___x_2655_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
lean_inc(v_j_2606_);
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v_j_2606_);
lean_ctor_set(v___x_2659_, 1, v_snd_2603_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v_fst_2598_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2661_, 0, v_ctorType_2605_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2662_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v_ctorType_2605_);
lean_dec(v_snd_2603_);
lean_dec(v_fst_2598_);
v_a_2668_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2655_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2655_);
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
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2597_ = stack[0].m_obj;
lean_object* v_fst_2598_ = stack[1].m_obj;
lean_object* v_struct_2599_ = stack[2].m_obj;
lean_object* v_structName_2600_ = stack[3].m_obj;
uint8_t v_a_2601_ = stack[4].m_num;
lean_object* v___f_2602_ = stack[5].m_obj;
lean_object* v_snd_2603_ = stack[6].m_obj;
lean_object* v_____r_2604_ = stack[7].m_obj;
lean_object* v_ctorType_2605_ = stack[8].m_obj;
lean_object* v_j_2606_ = stack[9].m_obj;
lean_object* v___y_2607_ = stack[10].m_obj;
lean_object* v___y_2608_ = stack[11].m_obj;
lean_object* v___y_2609_ = stack[12].m_obj;
lean_object* v___y_2610_ = stack[13].m_obj;
lean_object* v___y_2611_ = stack[14].m_obj;
lean_object* v___y_2612_ = stack[15].m_obj;
lean_object* v_res_2676_;
v_res_2676_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2597_, v_fst_2598_, v_struct_2599_, v_structName_2600_, v_a_2601_, v___f_2602_, v_snd_2603_, v_____r_2604_, v_ctorType_2605_, v_j_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2677_ = _args[0];
lean_object* v_fst_2678_ = _args[1];
lean_object* v_struct_2679_ = _args[2];
lean_object* v_structName_2680_ = _args[3];
lean_object* v_a_2681_ = _args[4];
lean_object* v___f_2682_ = _args[5];
lean_object* v_snd_2683_ = _args[6];
lean_object* v_____r_2684_ = _args[7];
lean_object* v_ctorType_2685_ = _args[8];
lean_object* v_j_2686_ = _args[9];
lean_object* v___y_2687_ = _args[10];
lean_object* v___y_2688_ = _args[11];
lean_object* v___y_2689_ = _args[12];
lean_object* v___y_2690_ = _args[13];
lean_object* v___y_2691_ = _args[14];
lean_object* v___y_2692_ = _args[15];
lean_object* v___y_2693_ = _args[16];
_start:
{
uint8_t v_a_19135__boxed_2694_; lean_object* v_res_2695_; 
v_a_19135__boxed_2694_ = lean_unbox(v_a_2681_);
v_res_2695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2677_, v_fst_2678_, v_struct_2679_, v_structName_2680_, v_a_19135__boxed_2694_, v___f_2682_, v_snd_2683_, v_____r_2684_, v_ctorType_2685_, v_j_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v_j_2686_);
return v_res_2695_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2696_, lean_object* v_struct_2697_, lean_object* v_structName_2698_, uint8_t v_a_2699_, lean_object* v_idx_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___y_2712_; uint8_t v___x_2734_; 
v___x_2734_ = lean_nat_dec_le(v_a_2702_, v_upperBound_2696_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_idx_2700_);
lean_dec(v_structName_2698_);
lean_dec_ref(v_struct_2697_);
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_b_2703_);
return v___x_2735_;
}
else
{
lean_object* v_snd_2736_; lean_object* v_snd_2737_; lean_object* v_fst_2738_; lean_object* v_fst_2739_; lean_object* v_fst_2740_; lean_object* v_snd_2741_; lean_object* v___f_2742_; uint8_t v___x_2743_; 
v_snd_2736_ = lean_ctor_get(v_b_2703_, 1);
lean_inc(v_snd_2736_);
v_snd_2737_ = lean_ctor_get(v_snd_2736_, 1);
lean_inc(v_snd_2737_);
v_fst_2738_ = lean_ctor_get(v_b_2703_, 0);
lean_inc(v_fst_2738_);
lean_dec_ref(v_b_2703_);
v_fst_2739_ = lean_ctor_get(v_snd_2736_, 0);
lean_inc(v_fst_2739_);
lean_dec(v_snd_2736_);
v_fst_2740_ = lean_ctor_get(v_snd_2737_, 0);
lean_inc(v_fst_2740_);
v_snd_2741_ = lean_ctor_get(v_snd_2737_, 1);
lean_inc(v_snd_2741_);
lean_dec(v_snd_2737_);
lean_inc_ref(v_a_2701_);
lean_inc(v_idx_2700_);
lean_inc(v_structName_2698_);
lean_inc_ref(v_struct_2697_);
v___f_2742_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2742_, 0, v_struct_2697_);
lean_closure_set(v___f_2742_, 1, v_structName_2698_);
lean_closure_set(v___f_2742_, 2, v_idx_2700_);
lean_closure_set(v___f_2742_, 3, v_a_2701_);
v___x_2743_ = l_Lean_Expr_isForall(v_fst_2738_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_expr_instantiate_rev_range(v_fst_2738_, v_fst_2740_, v_a_2702_, v_fst_2739_);
lean_dec(v_fst_2740_);
lean_dec(v_fst_2738_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2745_ = lean_whnf(v___x_2744_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = lean_box(0);
lean_inc(v_structName_2698_);
lean_inc_ref(v_struct_2697_);
lean_inc(v_a_2702_);
v___x_2748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2702_, v_fst_2739_, v_struct_2697_, v_structName_2698_, v_a_2699_, v___f_2742_, v_snd_2741_, v___x_2747_, v_a_2746_, v_a_2702_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
v___y_2712_ = v___x_2748_;
goto v___jp_2711_;
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v___f_2742_);
lean_dec(v_snd_2741_);
lean_dec(v_fst_2739_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_idx_2700_);
lean_dec(v_structName_2698_);
lean_dec_ref(v_struct_2697_);
v_a_2749_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2745_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2745_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_box(0);
lean_inc(v_structName_2698_);
lean_inc_ref(v_struct_2697_);
lean_inc(v_a_2702_);
v___x_2758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2702_, v_fst_2739_, v_struct_2697_, v_structName_2698_, v_a_2699_, v___f_2742_, v_snd_2741_, v___x_2757_, v_fst_2738_, v_fst_2740_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v_fst_2740_);
v___y_2712_ = v___x_2758_;
goto v___jp_2711_;
}
}
v___jp_2711_:
{
if (lean_obj_tag(v___y_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2725_; 
v_a_2713_ = lean_ctor_get(v___y_2712_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___y_2712_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2715_ = v___y_2712_;
v_isShared_2716_ = v_isSharedCheck_2725_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___y_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2725_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
if (lean_obj_tag(v_a_2713_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; 
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_idx_2700_);
lean_dec(v_structName_2698_);
lean_dec_ref(v_struct_2697_);
v_a_2717_ = lean_ctor_get(v_a_2713_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v_a_2713_, 1);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v_a_2717_);
v___x_2719_ = v___x_2715_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_del_object(v___x_2715_);
v_a_2721_ = lean_ctor_get(v_a_2713_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v_a_2713_, 1);
v___x_2722_ = lean_unsigned_to_nat(1u);
v___x_2723_ = lean_nat_add(v_a_2702_, v___x_2722_);
lean_dec(v_a_2702_);
v_a_2702_ = v___x_2723_;
v_b_2703_ = v_a_2721_;
goto _start;
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_idx_2700_);
lean_dec(v_structName_2698_);
lean_dec_ref(v_struct_2697_);
v_a_2726_ = lean_ctor_get(v___y_2712_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___y_2712_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___y_2712_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___y_2712_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2696_ = stack[0].m_obj;
lean_object* v_struct_2697_ = stack[1].m_obj;
lean_object* v_structName_2698_ = stack[2].m_obj;
uint8_t v_a_2699_ = stack[3].m_num;
lean_object* v_idx_2700_ = stack[4].m_obj;
lean_object* v_a_2701_ = stack[5].m_obj;
lean_object* v_a_2702_ = stack[6].m_obj;
lean_object* v_b_2703_ = stack[7].m_obj;
lean_object* v___y_2704_ = stack[8].m_obj;
lean_object* v___y_2705_ = stack[9].m_obj;
lean_object* v___y_2706_ = stack[10].m_obj;
lean_object* v___y_2707_ = stack[11].m_obj;
lean_object* v___y_2708_ = stack[12].m_obj;
lean_object* v___y_2709_ = stack[13].m_obj;
lean_object* v_res_2759_;
v_res_2759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2696_, v_struct_2697_, v_structName_2698_, v_a_2699_, v_idx_2700_, v_a_2701_, v_a_2702_, v_b_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
stack->m_obj
 = v_res_2759_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2760_, lean_object* v_struct_2761_, lean_object* v_structName_2762_, lean_object* v_a_2763_, lean_object* v_idx_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_b_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v_a_19373__boxed_2775_; lean_object* v_res_2776_; 
v_a_19373__boxed_2775_ = lean_unbox(v_a_2763_);
v_res_2776_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2760_, v_struct_2761_, v_structName_2762_, v_a_19373__boxed_2775_, v_idx_2764_, v_a_2765_, v_a_2766_, v_b_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec(v_upperBound_2760_);
return v_res_2776_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2779_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2780_ = lean_unsigned_to_nat(18u);
v___x_2781_ = lean_unsigned_to_nat(1913u);
v___x_2782_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2784_ = l_mkPanicMessageWithDecl(v___x_2783_, v___x_2782_, v___x_2781_, v___x_2780_, v___x_2779_);
return v___x_2784_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2785_);
return v___x_2787_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2789_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v___x_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2791_; lean_object* v_dummy_2792_; 
v___x_2791_ = lean_box(0);
v_dummy_2792_ = l_Lean_Expr_sort___override(v___x_2791_);
return v_dummy_2792_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2793_, lean_object* v_structName_2794_, lean_object* v_idx_2795_, lean_object* v_struct_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2811_; uint8_t v___x_2815_; 
v___x_2815_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2797_);
if (v___x_2815_ == 0)
{
lean_dec(v_idx_2795_);
lean_dec(v_structName_2794_);
if (lean_obj_tag(v_e_2793_) == 11)
{
lean_object* v_expr_2816_; lean_object* v_typeName_2817_; lean_object* v_idx_2818_; lean_object* v_struct_2819_; size_t v___x_2820_; size_t v___x_2821_; uint8_t v___x_2822_; 
v_expr_2816_ = lean_ctor_get(v_struct_2796_, 0);
lean_inc_ref(v_expr_2816_);
lean_dec_ref(v_struct_2796_);
v_typeName_2817_ = lean_ctor_get(v_e_2793_, 0);
v_idx_2818_ = lean_ctor_get(v_e_2793_, 1);
v_struct_2819_ = lean_ctor_get(v_e_2793_, 2);
v___x_2820_ = lean_ptr_addr(v_struct_2819_);
v___x_2821_ = lean_ptr_addr(v_expr_2816_);
v___x_2822_ = lean_usize_dec_eq(v___x_2820_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
lean_inc(v_idx_2818_);
lean_inc(v_typeName_2817_);
lean_dec_ref_known(v_e_2793_, 3);
v___x_2823_ = l_Lean_Expr_proj___override(v_typeName_2817_, v_idx_2818_, v_expr_2816_);
v___y_2811_ = v___x_2823_;
goto v___jp_2810_;
}
else
{
lean_dec_ref(v_expr_2816_);
v___y_2811_ = v_e_2793_;
goto v___jp_2810_;
}
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v_struct_2796_);
lean_dec_ref(v_e_2793_);
v___x_2824_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2825_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2824_);
v___y_2811_ = v___x_2825_;
goto v___jp_2810_;
}
}
else
{
lean_object* v___x_2826_; 
lean_inc_ref(v_struct_2796_);
v___x_2826_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2796_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
lean_inc(v_a_2802_);
lean_inc_ref(v_a_2801_);
lean_inc(v_a_2800_);
lean_inc_ref(v_a_2799_);
v___x_2828_ = lean_whnf(v_a_2827_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_n(v_a_2829_, 2);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = l_Lean_Meta_isProp(v_a_2829_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = l_Lean_Expr_getAppFn(v_a_2829_);
if (lean_obj_tag(v___x_2832_) == 4)
{
lean_object* v_declName_2833_; lean_object* v_us_2834_; lean_object* v___x_2835_; lean_object* v_env_2839_; uint8_t v___x_2840_; lean_object* v___x_2841_; 
v_declName_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_declName_2833_);
v_us_2834_ = lean_ctor_get(v___x_2832_, 1);
lean_inc(v_us_2834_);
lean_dec_ref_known(v___x_2832_, 2);
v___x_2835_ = lean_st_ref_get(v_a_2802_);
v_env_2839_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_ref(v_env_2839_);
lean_dec(v___x_2835_);
v___x_2840_ = 0;
v___x_2841_ = l_Lean_Environment_find_x3f(v_env_2839_, v_declName_2833_, v___x_2840_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
v___x_2842_ = lean_box(0);
v___x_2843_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2796_, v_structName_2794_, v_idx_2795_, v_a_2829_, lean_box(0), v___x_2842_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2843_;
}
else
{
lean_object* v_val_2844_; 
v_val_2844_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v___x_2841_, 1);
if (lean_obj_tag(v_val_2844_) == 5)
{
lean_object* v_val_2845_; lean_object* v_ctors_2846_; 
v_val_2845_ = lean_ctor_get(v_val_2844_, 0);
lean_inc_ref(v_val_2845_);
lean_dec_ref_known(v_val_2844_, 1);
v_ctors_2846_ = lean_ctor_get(v_val_2845_, 4);
lean_inc(v_ctors_2846_);
if (lean_obj_tag(v_ctors_2846_) == 1)
{
lean_object* v_tail_2847_; 
v_tail_2847_ = lean_ctor_get(v_ctors_2846_, 1);
if (lean_obj_tag(v_tail_2847_) == 0)
{
lean_object* v_toConstantVal_2848_; lean_object* v_numParams_2849_; lean_object* v_numIndices_2850_; lean_object* v_head_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2960_; 
v_toConstantVal_2848_ = lean_ctor_get(v_val_2845_, 0);
lean_inc_ref(v_toConstantVal_2848_);
v_numParams_2849_ = lean_ctor_get(v_val_2845_, 1);
lean_inc(v_numParams_2849_);
v_numIndices_2850_ = lean_ctor_get(v_val_2845_, 2);
lean_inc(v_numIndices_2850_);
lean_dec_ref(v_val_2845_);
v_head_2851_ = lean_ctor_get(v_ctors_2846_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_ctors_2846_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_ctors_2846_, 1);
lean_dec(v_unused_2961_);
v___x_2853_ = v_ctors_2846_;
v_isShared_2854_ = v_isSharedCheck_2960_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_head_2851_);
lean_dec(v_ctors_2846_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2960_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2851_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
if (lean_obj_tag(v_a_2856_) == 6)
{
lean_object* v_val_2857_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v_name_2938_; uint8_t v___x_2939_; 
v_val_2857_ = lean_ctor_get(v_a_2856_, 0);
lean_inc_ref(v_val_2857_);
lean_dec_ref_known(v_a_2856_, 1);
v_name_2938_ = lean_ctor_get(v_toConstantVal_2848_, 0);
lean_inc(v_name_2938_);
lean_dec_ref(v_toConstantVal_2848_);
v___x_2939_ = lean_name_eq(v_name_2938_, v_structName_2794_);
lean_dec(v_name_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v_val_2857_);
lean_del_object(v___x_2853_);
lean_dec(v_numIndices_2850_);
lean_dec(v_numParams_2849_);
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
v___x_2940_ = lean_box(0);
v___x_2941_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2796_, v_structName_2794_, v_idx_2795_, v_a_2829_, lean_box(0), v___x_2940_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
v___y_2913_ = v_a_2797_;
v___y_2914_ = v_a_2798_;
v___y_2915_ = v_a_2799_;
v___y_2916_ = v_a_2800_;
v___y_2917_ = v_a_2801_;
v___y_2918_ = v_a_2802_;
goto v___jp_2912_;
}
v___jp_2858_:
{
lean_object* v_toConstantVal_2866_; lean_object* v_name_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_toConstantVal_2866_ = lean_ctor_get(v_val_2857_, 0);
lean_inc_ref(v_toConstantVal_2866_);
lean_dec_ref(v_val_2857_);
v_name_2867_ = lean_ctor_get(v_toConstantVal_2866_, 0);
lean_inc(v_name_2867_);
lean_dec_ref(v_toConstantVal_2866_);
v___x_2868_ = l_Lean_mkConst(v_name_2867_, v_us_2834_);
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = l_Array_toSubarray___redArg(v___y_2859_, v___x_2869_, v_numParams_2849_);
v___x_2871_ = l_Subarray_copy___redArg(v___x_2870_);
v___x_2872_ = l_Lean_mkAppN(v___x_2868_, v___x_2871_);
lean_dec_ref(v___x_2871_);
lean_inc(v___y_2865_);
lean_inc_ref(v___y_2864_);
lean_inc(v___y_2863_);
lean_inc_ref(v___y_2862_);
v___x_2873_ = lean_infer_type(v___x_2872_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 0);
lean_ctor_set(v___x_2853_, 1, v___x_2875_);
lean_ctor_set(v___x_2853_, 0, v_a_2874_);
v___x_2877_ = v___x_2853_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2874_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
uint8_t v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_unbox(v_a_2831_);
lean_dec(v_a_2831_);
lean_inc_ref(v_struct_2796_);
lean_inc(v_idx_2795_);
v___x_2879_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2795_, v_struct_2796_, v_structName_2794_, v___x_2878_, v_idx_2795_, v_a_2829_, v___x_2869_, v___x_2877_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v_idx_2795_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v_snd_2881_; lean_object* v_snd_2882_; lean_object* v_snd_2883_; lean_object* v_expr_2884_; lean_object* v___x_2885_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v_snd_2881_ = lean_ctor_get(v_a_2880_, 1);
lean_inc(v_snd_2881_);
lean_dec(v_a_2880_);
v_snd_2882_ = lean_ctor_get(v_snd_2881_, 1);
lean_inc(v_snd_2882_);
lean_dec(v_snd_2881_);
v_snd_2883_ = lean_ctor_get(v_snd_2882_, 1);
lean_inc(v_snd_2883_);
lean_dec(v_snd_2882_);
v_expr_2884_ = lean_ctor_get(v_struct_2796_, 0);
lean_inc_ref(v_expr_2884_);
lean_dec_ref(v_struct_2796_);
v___x_2885_ = l_Lean_Expr_cleanupAnnotations(v_snd_2883_);
if (lean_obj_tag(v_e_2793_) == 11)
{
lean_object* v_typeName_2886_; lean_object* v_idx_2887_; lean_object* v_struct_2888_; size_t v___x_2889_; size_t v___x_2890_; uint8_t v___x_2891_; 
v_typeName_2886_ = lean_ctor_get(v_e_2793_, 0);
v_idx_2887_ = lean_ctor_get(v_e_2793_, 1);
v_struct_2888_ = lean_ctor_get(v_e_2793_, 2);
v___x_2889_ = lean_ptr_addr(v_struct_2888_);
v___x_2890_ = lean_ptr_addr(v_expr_2884_);
v___x_2891_ = lean_usize_dec_eq(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_inc(v_idx_2887_);
lean_inc(v_typeName_2886_);
lean_dec_ref_known(v_e_2793_, 3);
v___x_2892_ = l_Lean_Expr_proj___override(v_typeName_2886_, v_idx_2887_, v_expr_2884_);
v___y_2805_ = v___x_2885_;
v___y_2806_ = v___x_2892_;
goto v___jp_2804_;
}
else
{
lean_dec_ref(v_expr_2884_);
v___y_2805_ = v___x_2885_;
v___y_2806_ = v_e_2793_;
goto v___jp_2804_;
}
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref(v_expr_2884_);
lean_dec_ref(v_e_2793_);
v___x_2893_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2894_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2893_);
v___y_2805_ = v___x_2885_;
v___y_2806_ = v___x_2894_;
goto v___jp_2804_;
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v_struct_2796_);
lean_dec_ref(v_e_2793_);
v_a_2895_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2879_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2879_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_del_object(v___x_2853_);
lean_dec(v_a_2831_);
lean_dec(v_a_2829_);
lean_dec_ref(v_struct_2796_);
lean_dec(v_idx_2795_);
lean_dec(v_structName_2794_);
lean_dec_ref(v_e_2793_);
v_a_2904_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2873_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2873_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
v___jp_2912_:
{
lean_object* v_dummy_2919_; lean_object* v_nargs_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_dummy_2919_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2920_ = l_Lean_Expr_getAppNumArgs(v_a_2829_);
lean_inc(v_nargs_2920_);
v___x_2921_ = lean_mk_array(v_nargs_2920_, v_dummy_2919_);
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_sub(v_nargs_2920_, v___x_2922_);
lean_dec(v_nargs_2920_);
lean_inc(v_a_2829_);
v___x_2924_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2829_, v___x_2921_, v___x_2923_);
v___x_2925_ = lean_nat_add(v_numParams_2849_, v_numIndices_2850_);
lean_dec(v_numIndices_2850_);
v___x_2926_ = lean_array_get_size(v___x_2924_);
v___x_2927_ = lean_nat_dec_eq(v___x_2925_, v___x_2926_);
lean_dec(v___x_2925_);
if (v___x_2927_ == 0)
{
if (v___x_2815_ == 0)
{
v___y_2859_ = v___x_2924_;
v___y_2860_ = v___y_2913_;
v___y_2861_ = v___y_2914_;
v___y_2862_ = v___y_2915_;
v___y_2863_ = v___y_2916_;
v___y_2864_ = v___y_2917_;
v___y_2865_ = v___y_2918_;
goto v___jp_2858_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v___x_2924_);
lean_dec_ref(v_val_2857_);
lean_del_object(v___x_2853_);
lean_dec(v_numParams_2849_);
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
v___x_2928_ = lean_box(0);
v___x_2929_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2796_, v_structName_2794_, v_idx_2795_, v_a_2829_, lean_box(0), v___x_2928_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
v___y_2859_ = v___x_2924_;
v___y_2860_ = v___y_2913_;
v___y_2861_ = v___y_2914_;
v___y_2862_ = v___y_2915_;
v___y_2863_ = v___y_2916_;
v___y_2864_ = v___y_2917_;
v___y_2865_ = v___y_2918_;
goto v___jp_2858_;
}
}
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_dec(v_a_2856_);
lean_del_object(v___x_2853_);
lean_dec(v_numIndices_2850_);
lean_dec(v_numParams_2849_);
lean_dec_ref(v_toConstantVal_2848_);
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
v___x_2950_ = lean_box(0);
v___x_2951_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2796_, v_structName_2794_, v_idx_2795_, v_a_2829_, lean_box(0), v___x_2950_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2951_;
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_del_object(v___x_2853_);
lean_dec(v_numIndices_2850_);
lean_dec(v_numParams_2849_);
lean_dec_ref(v_toConstantVal_2848_);
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec(v_a_2829_);
lean_dec_ref(v_struct_2796_);
lean_dec(v_idx_2795_);
lean_dec(v_structName_2794_);
lean_dec_ref(v_e_2793_);
v_a_2952_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2855_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2855_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2846_, 2);
lean_dec_ref(v_val_2845_);
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
goto v___jp_2836_;
}
}
else
{
lean_dec(v_ctors_2846_);
lean_dec_ref(v_val_2845_);
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
goto v___jp_2836_;
}
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec(v_val_2844_);
lean_dec(v_us_2834_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
v___x_2962_ = lean_box(0);
v___x_2963_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2796_, v_structName_2794_, v_idx_2795_, v_a_2829_, lean_box(0), v___x_2962_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2963_;
}
}
v___jp_2836_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_box(0);
v___x_2838_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2796_, v_structName_2794_, v_idx_2795_, v_a_2829_, lean_box(0), v___x_2837_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2838_;
}
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v___x_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_e_2793_);
v___x_2964_ = lean_box(0);
v___x_2965_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2796_, v_structName_2794_, v_idx_2795_, v_a_2829_, lean_box(0), v___x_2964_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2965_;
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_a_2829_);
lean_dec_ref(v_struct_2796_);
lean_dec(v_idx_2795_);
lean_dec(v_structName_2794_);
lean_dec_ref(v_e_2793_);
v_a_2966_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2830_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2830_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v_struct_2796_);
lean_dec(v_idx_2795_);
lean_dec(v_structName_2794_);
lean_dec_ref(v_e_2793_);
v_a_2974_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2828_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2828_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref(v_struct_2796_);
lean_dec(v_idx_2795_);
lean_dec(v_structName_2794_);
lean_dec_ref(v_e_2793_);
v_a_2982_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2826_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2826_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
v___jp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___y_2805_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___y_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
v___jp_2810_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = lean_box(0);
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___y_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2793_ = stack[0].m_obj;
lean_object* v_structName_2794_ = stack[1].m_obj;
lean_object* v_idx_2795_ = stack[2].m_obj;
lean_object* v_struct_2796_ = stack[3].m_obj;
lean_object* v_a_2797_ = stack[4].m_obj;
lean_object* v_a_2798_ = stack[5].m_obj;
lean_object* v_a_2799_ = stack[6].m_obj;
lean_object* v_a_2800_ = stack[7].m_obj;
lean_object* v_a_2801_ = stack[8].m_obj;
lean_object* v_a_2802_ = stack[9].m_obj;
lean_object* v_res_2990_;
v_res_2990_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2793_, v_structName_2794_, v_idx_2795_, v_struct_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
stack->m_obj
 = v_res_2990_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2991_, lean_object* v_structName_2992_, lean_object* v_idx_2993_, lean_object* v_struct_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2991_, v_structName_2992_, v_idx_2993_, v_struct_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec(v_a_2995_);
return v_res_3002_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_3003_, lean_object* v_struct_3004_, lean_object* v_structName_3005_, uint8_t v_a_3006_, lean_object* v_idx_3007_, lean_object* v_a_3008_, lean_object* v_inst_3009_, lean_object* v_R_3010_, lean_object* v_a_3011_, lean_object* v_b_3012_, lean_object* v_c_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_3003_, v_struct_3004_, v_structName_3005_, v_a_3006_, v_idx_3007_, v_a_3008_, v_a_3011_, v_b_3012_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3003_ = stack[0].m_obj;
lean_object* v_struct_3004_ = stack[1].m_obj;
lean_object* v_structName_3005_ = stack[2].m_obj;
uint8_t v_a_3006_ = stack[3].m_num;
lean_object* v_idx_3007_ = stack[4].m_obj;
lean_object* v_a_3008_ = stack[5].m_obj;
lean_object* v_a_3011_ = stack[8].m_obj;
lean_object* v_b_3012_ = stack[9].m_obj;
lean_object* v___y_3014_ = stack[11].m_obj;
lean_object* v___y_3015_ = stack[12].m_obj;
lean_object* v___y_3016_ = stack[13].m_obj;
lean_object* v___y_3017_ = stack[14].m_obj;
lean_object* v___y_3018_ = stack[15].m_obj;
lean_object* v___y_3019_ = stack[16].m_obj;
lean_object* v_res_3022_;
v_res_3022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_3003_, v_struct_3004_, v_structName_3005_, v_a_3006_, v_idx_3007_, v_a_3008_, lean_box(0), lean_box(0), v_a_3011_, v_b_3012_, lean_box(0), v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
stack->m_obj
 = v_res_3022_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_3023_ = _args[0];
lean_object* v_struct_3024_ = _args[1];
lean_object* v_structName_3025_ = _args[2];
lean_object* v_a_3026_ = _args[3];
lean_object* v_idx_3027_ = _args[4];
lean_object* v_a_3028_ = _args[5];
lean_object* v_inst_3029_ = _args[6];
lean_object* v_R_3030_ = _args[7];
lean_object* v_a_3031_ = _args[8];
lean_object* v_b_3032_ = _args[9];
lean_object* v_c_3033_ = _args[10];
lean_object* v___y_3034_ = _args[11];
lean_object* v___y_3035_ = _args[12];
lean_object* v___y_3036_ = _args[13];
lean_object* v___y_3037_ = _args[14];
lean_object* v___y_3038_ = _args[15];
lean_object* v___y_3039_ = _args[16];
lean_object* v___y_3040_ = _args[17];
_start:
{
uint8_t v_a_20147__boxed_3041_; lean_object* v_res_3042_; 
v_a_20147__boxed_3041_ = lean_unbox(v_a_3026_);
v_res_3042_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_3023_, v_struct_3024_, v_structName_3025_, v_a_20147__boxed_3041_, v_idx_3027_, v_a_3028_, v_inst_3029_, v_R_3030_, v_a_3031_, v_b_3032_, v_c_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec(v_upperBound_3023_);
return v_res_3042_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_3043_, size_t v_i_3044_, size_t v_stop_3045_, lean_object* v_b_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_usize_dec_eq(v_i_3044_, v_stop_3045_);
if (v___x_3053_ == 0)
{
size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3054_ = ((size_t)1ULL);
v___x_3055_ = lean_usize_sub(v_i_3044_, v___x_3054_);
v___x_3056_ = lean_array_uget_borrowed(v_as_3043_, v___x_3055_);
lean_inc(v___x_3056_);
v___x_3057_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_3056_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3059_ = l_Lean_Expr_sortLevel_x21(v_a_3058_);
lean_dec(v_a_3058_);
v___x_3060_ = l_Lean_mkLevelIMax_x27(v___x_3059_, v_b_3046_);
v_i_3044_ = v___x_3055_;
v_b_3046_ = v___x_3060_;
goto _start;
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v_b_3046_);
v_a_3062_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3057_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3057_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
else
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_b_3046_);
return v___x_3070_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3043_ = stack[0].m_obj;
size_t v_i_3044_ = stack[1].m_num;
size_t v_stop_3045_ = stack[2].m_num;
lean_object* v_b_3046_ = stack[3].m_obj;
lean_object* v___y_3047_ = stack[4].m_obj;
lean_object* v___y_3048_ = stack[5].m_obj;
lean_object* v___y_3049_ = stack[6].m_obj;
lean_object* v___y_3050_ = stack[7].m_obj;
lean_object* v___y_3051_ = stack[8].m_obj;
lean_object* v_res_3071_;
v_res_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3043_, v_i_3044_, v_stop_3045_, v_b_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
stack->m_obj
 = v_res_3071_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_3072_, lean_object* v_i_3073_, lean_object* v_stop_3074_, lean_object* v_b_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
size_t v_i_boxed_3082_; size_t v_stop_boxed_3083_; lean_object* v_res_3084_; 
v_i_boxed_3082_ = lean_unbox_usize(v_i_3073_);
lean_dec(v_i_3073_);
v_stop_boxed_3083_ = lean_unbox_usize(v_stop_3074_);
lean_dec(v_stop_3074_);
v_res_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3072_, v_i_boxed_3082_, v_stop_boxed_3083_, v_b_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v_as_3072_);
return v_res_3084_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_3089_ = lean_unsigned_to_nat(14u);
v___x_3090_ = lean_unsigned_to_nat(22u);
v___x_3091_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_3093_ = l_mkPanicMessageWithDecl(v___x_3092_, v___x_3091_, v___x_3090_, v___x_3089_, v___x_3088_);
return v___x_3093_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_3094_, lean_object* v_doms_3095_, lean_object* v_body_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_lctx_3104_; lean_object* v_expr_3105_; uint8_t v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v_a_3110_; uint8_t v___x_3115_; 
v_lctx_3104_ = lean_ctor_get(v_a_3099_, 2);
v_expr_3105_ = lean_ctor_get(v_body_3096_, 0);
v___x_3106_ = 1;
v___x_3107_ = 0;
lean_inc_ref(v_lctx_3104_);
v___x_3108_ = l_Lean_LocalContext_mkForall(v_lctx_3104_, v_fvars_3094_, v_expr_3105_, v___x_3106_, v___x_3107_);
v___x_3115_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3097_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3124_; 
v_isSharedCheck_3124_ = !lean_is_exclusive(v_body_3096_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; lean_object* v_unused_3126_; 
v_unused_3125_ = lean_ctor_get(v_body_3096_, 1);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_body_3096_, 0);
lean_dec(v_unused_3126_);
v___x_3117_ = v_body_3096_;
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
else
{
lean_dec(v_body_3096_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3119_ = lean_box(0);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3119_);
lean_ctor_set(v___x_3117_, 0, v___x_3108_);
v___x_3121_ = v___x_3117_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
return v___x_3122_;
}
}
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___y_3130_; lean_object* v_type_x3f_3147_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v_type_x3f_3147_ = lean_ctor_get(v_a_3128_, 1);
lean_inc(v_type_x3f_3147_);
lean_dec(v_a_3128_);
if (lean_obj_tag(v_type_x3f_3147_) == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3149_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3148_);
v___y_3130_ = v___x_3149_;
goto v___jp_3129_;
}
else
{
lean_object* v_val_3150_; 
v_val_3150_ = lean_ctor_get(v_type_x3f_3147_, 0);
lean_inc(v_val_3150_);
lean_dec_ref_known(v_type_x3f_3147_, 1);
v___y_3130_ = v_val_3150_;
goto v___jp_3129_;
}
v___jp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3131_ = l_Lean_Expr_sortLevel_x21(v___y_3130_);
lean_dec_ref(v___y_3130_);
v___x_3132_ = lean_array_get_size(v_doms_3095_);
v___x_3133_ = lean_unsigned_to_nat(0u);
v___x_3134_ = lean_nat_dec_lt(v___x_3133_, v___x_3132_);
if (v___x_3134_ == 0)
{
v_a_3110_ = v___x_3131_;
goto v___jp_3109_;
}
else
{
size_t v___x_3135_; size_t v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_usize_of_nat(v___x_3132_);
v___x_3136_ = ((size_t)0ULL);
v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_3095_, v___x_3135_, v___x_3136_, v___x_3131_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v_a_3110_ = v_a_3138_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v___x_3108_);
v_a_3139_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3137_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3137_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3108_);
return v___x_3127_;
}
}
v___jp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3111_ = l_Lean_Expr_sort___override(v_a_3110_);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3108_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
return v___x_3114_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3094_ = stack[0].m_obj;
lean_object* v_doms_3095_ = stack[1].m_obj;
lean_object* v_body_3096_ = stack[2].m_obj;
lean_object* v_a_3097_ = stack[3].m_obj;
lean_object* v_a_3098_ = stack[4].m_obj;
lean_object* v_a_3099_ = stack[5].m_obj;
lean_object* v_a_3100_ = stack[6].m_obj;
lean_object* v_a_3101_ = stack[7].m_obj;
lean_object* v_a_3102_ = stack[8].m_obj;
lean_object* v_res_3151_;
v_res_3151_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3094_, v_doms_3095_, v_body_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
stack->m_obj
 = v_res_3151_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3152_, lean_object* v_doms_3153_, lean_object* v_body_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3152_, v_doms_3153_, v_body_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_doms_3153_);
lean_dec_ref(v_fvars_3152_);
return v_res_3162_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3163_, size_t v_i_3164_, size_t v_stop_3165_, lean_object* v_b_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3163_, v_i_3164_, v_stop_3165_, v_b_3166_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3163_ = stack[0].m_obj;
size_t v_i_3164_ = stack[1].m_num;
size_t v_stop_3165_ = stack[2].m_num;
lean_object* v_b_3166_ = stack[3].m_obj;
lean_object* v___y_3167_ = stack[4].m_obj;
lean_object* v___y_3168_ = stack[5].m_obj;
lean_object* v___y_3169_ = stack[6].m_obj;
lean_object* v___y_3170_ = stack[7].m_obj;
lean_object* v___y_3171_ = stack[8].m_obj;
lean_object* v___y_3172_ = stack[9].m_obj;
lean_object* v_res_3175_;
v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3163_, v_i_3164_, v_stop_3165_, v_b_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
stack->m_obj
 = v_res_3175_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3176_, lean_object* v_i_3177_, lean_object* v_stop_3178_, lean_object* v_b_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
size_t v_i_boxed_3187_; size_t v_stop_boxed_3188_; lean_object* v_res_3189_; 
v_i_boxed_3187_ = lean_unbox_usize(v_i_3177_);
lean_dec(v_i_3177_);
v_stop_boxed_3188_ = lean_unbox_usize(v_stop_3178_);
lean_dec(v_stop_3178_);
v_res_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3176_, v_i_boxed_3187_, v_stop_boxed_3188_, v_b_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v_as_3176_);
return v_res_3189_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3190_, lean_object* v_opt_3191_){
_start:
{
lean_object* v_name_3192_; lean_object* v_defValue_3193_; lean_object* v_map_3194_; lean_object* v___x_3195_; 
v_name_3192_ = lean_ctor_get(v_opt_3191_, 0);
v_defValue_3193_ = lean_ctor_get(v_opt_3191_, 1);
v_map_3194_ = lean_ctor_get(v_opts_3190_, 0);
v___x_3195_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3194_, v_name_3192_);
if (lean_obj_tag(v___x_3195_) == 0)
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_unbox(v_defValue_3193_);
return v___x_3196_;
}
else
{
lean_object* v_val_3197_; 
v_val_3197_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_val_3197_);
lean_dec_ref_known(v___x_3195_, 1);
if (lean_obj_tag(v_val_3197_) == 1)
{
uint8_t v_v_3198_; 
v_v_3198_ = lean_ctor_get_uint8(v_val_3197_, 0);
lean_dec_ref_known(v_val_3197_, 0);
return v_v_3198_;
}
else
{
uint8_t v___x_3199_; 
lean_dec(v_val_3197_);
v___x_3199_ = lean_unbox(v_defValue_3193_);
return v___x_3199_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_3190_ = stack[0].m_obj;
lean_object* v_opt_3191_ = stack[1].m_obj;
uint8_t v_res_3200_;
v_res_3200_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3190_, v_opt_3191_);
stack->m_num = v_res_3200_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3201_, lean_object* v_opt_3202_){
_start:
{
uint8_t v_res_3203_; lean_object* v_r_3204_; 
v_res_3203_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3201_, v_opt_3202_);
lean_dec_ref(v_opt_3202_);
lean_dec_ref(v_opts_3201_);
v_r_3204_ = lean_box(v_res_3203_);
return v_r_3204_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3205_){
_start:
{
if (lean_obj_tag(v_x_3205_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_a_3207_ = lean_ctor_get(v_x_3205_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_x_3205_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v_x_3205_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v_x_3205_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
v_a_3215_ = lean_ctor_get(v_x_3205_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_x_3205_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v_x_3205_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v_x_3205_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set_tag(v___x_3217_, 0);
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3205_ = stack[0].m_obj;
lean_object* v_res_3223_;
v_res_3223_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3205_);
stack->m_obj
 = v_res_3223_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3224_);
return v_res_3226_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3227_){
_start:
{
if (lean_obj_tag(v_e_3227_) == 0)
{
uint8_t v___x_3228_; 
v___x_3228_ = 2;
return v___x_3228_;
}
else
{
uint8_t v___x_3229_; 
v___x_3229_ = 0;
return v___x_3229_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3227_ = stack[0].m_obj;
uint8_t v_res_3230_;
v_res_3230_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3227_);
stack->m_num = v_res_3230_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3231_){
_start:
{
uint8_t v_res_3232_; lean_object* v_r_3233_; 
v_res_3232_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3231_);
lean_dec_ref(v_e_3231_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3234_, lean_object* v_opt_3235_){
_start:
{
lean_object* v_name_3236_; lean_object* v_defValue_3237_; lean_object* v_map_3238_; lean_object* v___x_3239_; 
v_name_3236_ = lean_ctor_get(v_opt_3235_, 0);
v_defValue_3237_ = lean_ctor_get(v_opt_3235_, 1);
v_map_3238_ = lean_ctor_get(v_opts_3234_, 0);
v___x_3239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3238_, v_name_3236_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_inc(v_defValue_3237_);
return v_defValue_3237_;
}
else
{
lean_object* v_val_3240_; 
v_val_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_val_3240_);
lean_dec_ref_known(v___x_3239_, 1);
if (lean_obj_tag(v_val_3240_) == 3)
{
lean_object* v_v_3241_; 
v_v_3241_ = lean_ctor_get(v_val_3240_, 0);
lean_inc(v_v_3241_);
lean_dec_ref_known(v_val_3240_, 1);
return v_v_3241_;
}
else
{
lean_dec(v_val_3240_);
lean_inc(v_defValue_3237_);
return v_defValue_3237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3242_, lean_object* v_opt_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3242_, v_opt_3243_);
lean_dec_ref(v_opt_3243_);
lean_dec_ref(v_opts_3242_);
return v_res_3244_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3245_, size_t v_i_3246_, lean_object* v_bs_3247_){
_start:
{
uint8_t v___x_3248_; 
v___x_3248_ = lean_usize_dec_lt(v_i_3246_, v_sz_3245_);
if (v___x_3248_ == 0)
{
return v_bs_3247_;
}
else
{
lean_object* v_v_3249_; lean_object* v_msg_3250_; lean_object* v___x_3251_; lean_object* v_bs_x27_3252_; size_t v___x_3253_; size_t v___x_3254_; lean_object* v___x_3255_; 
v_v_3249_ = lean_array_uget_borrowed(v_bs_3247_, v_i_3246_);
v_msg_3250_ = lean_ctor_get(v_v_3249_, 1);
lean_inc_ref(v_msg_3250_);
v___x_3251_ = lean_unsigned_to_nat(0u);
v_bs_x27_3252_ = lean_array_uset(v_bs_3247_, v_i_3246_, v___x_3251_);
v___x_3253_ = ((size_t)1ULL);
v___x_3254_ = lean_usize_add(v_i_3246_, v___x_3253_);
v___x_3255_ = lean_array_uset(v_bs_x27_3252_, v_i_3246_, v_msg_3250_);
v_i_3246_ = v___x_3254_;
v_bs_3247_ = v___x_3255_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3245_ = stack[0].m_num;
size_t v_i_3246_ = stack[1].m_num;
lean_object* v_bs_3247_ = stack[2].m_obj;
lean_object* v_res_3257_;
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3245_, v_i_3246_, v_bs_3247_);
stack->m_obj
 = v_res_3257_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3258_, lean_object* v_i_3259_, lean_object* v_bs_3260_){
_start:
{
size_t v_sz_boxed_3261_; size_t v_i_boxed_3262_; lean_object* v_res_3263_; 
v_sz_boxed_3261_ = lean_unbox_usize(v_sz_3258_);
lean_dec(v_sz_3258_);
v_i_boxed_3262_ = lean_unbox_usize(v_i_3259_);
lean_dec(v_i_3259_);
v_res_3263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3261_, v_i_boxed_3262_, v_bs_3260_);
return v_res_3263_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3264_, lean_object* v_data_3265_, lean_object* v_ref_3266_, lean_object* v_msg_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_toCold_3273_; lean_object* v_currRecDepth_3274_; lean_object* v_ref_3275_; uint16_t v_optionFlags_3276_; uint8_t v_suppressElabErrors_3277_; uint8_t v_isRecordingDeps_3278_; lean_object* v_ref_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v_traceState_3282_; lean_object* v_traces_3283_; lean_object* v___x_3284_; size_t v_sz_3285_; size_t v___x_3286_; lean_object* v___x_3287_; lean_object* v_msg_3288_; lean_object* v___x_3289_; lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3328_; 
v_toCold_3273_ = lean_ctor_get(v___y_3270_, 0);
v_currRecDepth_3274_ = lean_ctor_get(v___y_3270_, 1);
v_ref_3275_ = lean_ctor_get(v___y_3270_, 2);
v_optionFlags_3276_ = lean_ctor_get_uint16(v___y_3270_, sizeof(void*)*3);
v_suppressElabErrors_3277_ = lean_ctor_get_uint8(v___y_3270_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3278_ = lean_ctor_get_uint8(v___y_3270_, sizeof(void*)*3 + 3);
v_ref_3279_ = l_Lean_replaceRef(v_ref_3266_, v_ref_3275_);
lean_inc(v_currRecDepth_3274_);
lean_inc_ref(v_toCold_3273_);
v___x_3280_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3280_, 0, v_toCold_3273_);
lean_ctor_set(v___x_3280_, 1, v_currRecDepth_3274_);
lean_ctor_set(v___x_3280_, 2, v_ref_3279_);
lean_ctor_set_uint16(v___x_3280_, sizeof(void*)*3, v_optionFlags_3276_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*3 + 2, v_suppressElabErrors_3277_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*3 + 3, v_isRecordingDeps_3278_);
v___x_3281_ = lean_st_ref_get(v___y_3271_);
v_traceState_3282_ = lean_ctor_get(v___x_3281_, 4);
lean_inc_ref(v_traceState_3282_);
lean_dec(v___x_3281_);
v_traces_3283_ = lean_ctor_get(v_traceState_3282_, 0);
lean_inc_ref(v_traces_3283_);
lean_dec_ref(v_traceState_3282_);
v___x_3284_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3283_);
lean_dec_ref(v_traces_3283_);
v_sz_3285_ = lean_array_size(v___x_3284_);
v___x_3286_ = ((size_t)0ULL);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3285_, v___x_3286_, v___x_3284_);
v_msg_3288_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3288_, 0, v_data_3265_);
lean_ctor_set(v_msg_3288_, 1, v_msg_3267_);
lean_ctor_set(v_msg_3288_, 2, v___x_3287_);
v___x_3289_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3288_, v___y_3268_, v___y_3269_, v___x_3280_, v___y_3271_);
lean_dec_ref_known(v___x_3280_, 3);
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3328_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3328_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v_traceState_3295_; lean_object* v_env_3296_; lean_object* v_nextMacroScope_3297_; lean_object* v_ngen_3298_; lean_object* v_auxDeclNGen_3299_; lean_object* v_cache_3300_; lean_object* v_recordedDeps_3301_; lean_object* v_messages_3302_; lean_object* v_infoState_3303_; lean_object* v_snapshotTasks_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3327_; 
v___x_3294_ = lean_st_ref_take(v___y_3271_);
v_traceState_3295_ = lean_ctor_get(v___x_3294_, 4);
v_env_3296_ = lean_ctor_get(v___x_3294_, 0);
v_nextMacroScope_3297_ = lean_ctor_get(v___x_3294_, 1);
v_ngen_3298_ = lean_ctor_get(v___x_3294_, 2);
v_auxDeclNGen_3299_ = lean_ctor_get(v___x_3294_, 3);
v_cache_3300_ = lean_ctor_get(v___x_3294_, 5);
v_recordedDeps_3301_ = lean_ctor_get(v___x_3294_, 6);
v_messages_3302_ = lean_ctor_get(v___x_3294_, 7);
v_infoState_3303_ = lean_ctor_get(v___x_3294_, 8);
v_snapshotTasks_3304_ = lean_ctor_get(v___x_3294_, 9);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3306_ = v___x_3294_;
v_isShared_3307_ = v_isSharedCheck_3327_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_snapshotTasks_3304_);
lean_inc(v_infoState_3303_);
lean_inc(v_messages_3302_);
lean_inc(v_recordedDeps_3301_);
lean_inc(v_cache_3300_);
lean_inc(v_traceState_3295_);
lean_inc(v_auxDeclNGen_3299_);
lean_inc(v_ngen_3298_);
lean_inc(v_nextMacroScope_3297_);
lean_inc(v_env_3296_);
lean_dec(v___x_3294_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3327_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
uint64_t v_tid_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3325_; 
v_tid_3308_ = lean_ctor_get_uint64(v_traceState_3295_, sizeof(void*)*1);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_traceState_3295_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; 
v_unused_3326_ = lean_ctor_get(v_traceState_3295_, 0);
lean_dec(v_unused_3326_);
v___x_3310_ = v_traceState_3295_;
v_isShared_3311_ = v_isSharedCheck_3325_;
goto v_resetjp_3309_;
}
else
{
lean_dec(v_traceState_3295_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3325_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_ref_3266_);
lean_ctor_set(v___x_3313_, 1, v_a_3290_);
v___x_3314_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3264_, v___x_3313_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3314_);
v___x_3316_ = v___x_3310_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3314_);
lean_ctor_set_uint64(v_reuseFailAlloc_3324_, sizeof(void*)*1, v_tid_3308_);
v___x_3316_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3316_);
v___x_3318_ = v___x_3306_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_env_3296_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_nextMacroScope_3297_);
lean_ctor_set(v_reuseFailAlloc_3323_, 2, v_ngen_3298_);
lean_ctor_set(v_reuseFailAlloc_3323_, 3, v_auxDeclNGen_3299_);
lean_ctor_set(v_reuseFailAlloc_3323_, 4, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3323_, 5, v_cache_3300_);
lean_ctor_set(v_reuseFailAlloc_3323_, 6, v_recordedDeps_3301_);
lean_ctor_set(v_reuseFailAlloc_3323_, 7, v_messages_3302_);
lean_ctor_set(v_reuseFailAlloc_3323_, 8, v_infoState_3303_);
lean_ctor_set(v_reuseFailAlloc_3323_, 9, v_snapshotTasks_3304_);
v___x_3318_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3319_ = lean_st_ref_put(v___y_3271_, v___x_3318_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3312_);
v___x_3321_ = v___x_3292_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3312_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_3264_ = stack[0].m_obj;
lean_object* v_data_3265_ = stack[1].m_obj;
lean_object* v_ref_3266_ = stack[2].m_obj;
lean_object* v_msg_3267_ = stack[3].m_obj;
lean_object* v___y_3268_ = stack[4].m_obj;
lean_object* v___y_3269_ = stack[5].m_obj;
lean_object* v___y_3270_ = stack[6].m_obj;
lean_object* v___y_3271_ = stack[7].m_obj;
lean_object* v_res_3329_;
v_res_3329_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3264_, v_data_3265_, v_ref_3266_, v_msg_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
stack->m_obj
 = v_res_3329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3330_, lean_object* v_data_3331_, lean_object* v_ref_3332_, lean_object* v_msg_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3330_, v_data_3331_, v_ref_3332_, v_msg_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
return v_res_3339_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3342_ = l_Lean_stringToMessageData(v___x_3341_);
return v___x_3342_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3343_; double v___x_3344_; 
v___x_3343_ = lean_unsigned_to_nat(1000u);
v___x_3344_ = lean_float_of_nat(v___x_3343_);
return v___x_3344_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3345_, uint8_t v_collapsed_3346_, lean_object* v_tag_3347_, lean_object* v_opts_3348_, uint8_t v_clsEnabled_3349_, lean_object* v_oldTraces_3350_, lean_object* v_msg_3351_, lean_object* v_resStartStop_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v_data_3365_; lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___y_3381_; lean_object* v_a_3382_; uint8_t v___y_3397_; double v___y_3429_; 
v_fst_3360_ = lean_ctor_get(v_resStartStop_3352_, 0);
lean_inc(v_fst_3360_);
v_snd_3361_ = lean_ctor_get(v_resStartStop_3352_, 1);
lean_inc(v_snd_3361_);
lean_dec_ref(v_resStartStop_3352_);
v_fst_3376_ = lean_ctor_get(v_snd_3361_, 0);
lean_inc(v_fst_3376_);
v_snd_3377_ = lean_ctor_get(v_snd_3361_, 1);
lean_inc(v_snd_3377_);
lean_dec(v_snd_3361_);
v___x_3378_ = l_Lean_trace_profiler;
v___x_3379_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3348_, v___x_3378_);
if (v___x_3379_ == 0)
{
v___y_3397_ = v___x_3379_;
goto v___jp_3396_;
}
else
{
lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3435_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3348_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; double v___x_3438_; double v___x_3439_; double v___x_3440_; 
v___x_3436_ = l_Lean_trace_profiler_threshold;
v___x_3437_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3348_, v___x_3436_);
v___x_3438_ = lean_float_of_nat(v___x_3437_);
v___x_3439_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3440_ = lean_float_div(v___x_3438_, v___x_3439_);
v___y_3429_ = v___x_3440_;
goto v___jp_3428_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; double v___x_3443_; 
v___x_3441_ = l_Lean_trace_profiler_threshold;
v___x_3442_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3348_, v___x_3441_);
v___x_3443_ = lean_float_of_nat(v___x_3442_);
v___y_3429_ = v___x_3443_;
goto v___jp_3428_;
}
}
v___jp_3362_:
{
lean_object* v___x_3366_; 
lean_inc(v___y_3363_);
v___x_3366_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3350_, v_data_3365_, v___y_3363_, v___y_3364_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; 
lean_dec_ref_known(v___x_3366_, 1);
v___x_3367_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3360_);
return v___x_3367_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v_fst_3360_);
v_a_3368_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3366_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
v___jp_3380_:
{
uint8_t v_result_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; double v___x_3386_; lean_object* v_data_3387_; 
v_result_3383_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3360_);
v___x_3384_ = lean_box(v_result_3383_);
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
v___x_3386_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3347_);
lean_inc_ref(v___x_3385_);
lean_inc(v_cls_3345_);
v_data_3387_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3387_, 0, v_cls_3345_);
lean_ctor_set(v_data_3387_, 1, v___x_3385_);
lean_ctor_set(v_data_3387_, 2, v_tag_3347_);
lean_ctor_set_float(v_data_3387_, sizeof(void*)*3, v___x_3386_);
lean_ctor_set_float(v_data_3387_, sizeof(void*)*3 + 8, v___x_3386_);
lean_ctor_set_uint8(v_data_3387_, sizeof(void*)*3 + 16, v_collapsed_3346_);
if (v___x_3379_ == 0)
{
lean_dec_ref_known(v___x_3385_, 1);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec_ref(v_tag_3347_);
lean_dec(v_cls_3345_);
v___y_3363_ = v___y_3381_;
v___y_3364_ = v_a_3382_;
v_data_3365_ = v_data_3387_;
goto v___jp_3362_;
}
else
{
lean_object* v_data_3388_; double v___x_3389_; double v___x_3390_; 
lean_dec_ref_known(v_data_3387_, 3);
v_data_3388_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3388_, 0, v_cls_3345_);
lean_ctor_set(v_data_3388_, 1, v___x_3385_);
lean_ctor_set(v_data_3388_, 2, v_tag_3347_);
v___x_3389_ = lean_unbox_float(v_fst_3376_);
lean_dec(v_fst_3376_);
lean_ctor_set_float(v_data_3388_, sizeof(void*)*3, v___x_3389_);
v___x_3390_ = lean_unbox_float(v_snd_3377_);
lean_dec(v_snd_3377_);
lean_ctor_set_float(v_data_3388_, sizeof(void*)*3 + 8, v___x_3390_);
lean_ctor_set_uint8(v_data_3388_, sizeof(void*)*3 + 16, v_collapsed_3346_);
v___y_3363_ = v___y_3381_;
v___y_3364_ = v_a_3382_;
v_data_3365_ = v_data_3388_;
goto v___jp_3362_;
}
}
v___jp_3391_:
{
lean_object* v_ref_3392_; lean_object* v___x_3393_; 
v_ref_3392_ = lean_ctor_get(v___y_3357_, 2);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
lean_inc(v___y_3356_);
lean_inc_ref(v___y_3355_);
lean_inc(v___y_3354_);
lean_inc(v___y_3353_);
lean_inc(v_fst_3360_);
v___x_3393_ = lean_apply_8(v_msg_3351_, v_fst_3360_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, lean_box(0));
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___y_3381_ = v_ref_3392_;
v_a_3382_ = v_a_3394_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3395_; 
lean_dec_ref_known(v___x_3393_, 1);
v___x_3395_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3381_ = v_ref_3392_;
v_a_3382_ = v___x_3395_;
goto v___jp_3380_;
}
}
v___jp_3396_:
{
if (v_clsEnabled_3349_ == 0)
{
if (v___y_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v_traceState_3399_; lean_object* v_env_3400_; lean_object* v_nextMacroScope_3401_; lean_object* v_ngen_3402_; lean_object* v_auxDeclNGen_3403_; lean_object* v_cache_3404_; lean_object* v_recordedDeps_3405_; lean_object* v_messages_3406_; lean_object* v_infoState_3407_; lean_object* v_snapshotTasks_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3427_; 
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec_ref(v_msg_3351_);
lean_dec_ref(v_tag_3347_);
lean_dec(v_cls_3345_);
v___x_3398_ = lean_st_ref_take(v___y_3358_);
v_traceState_3399_ = lean_ctor_get(v___x_3398_, 4);
v_env_3400_ = lean_ctor_get(v___x_3398_, 0);
v_nextMacroScope_3401_ = lean_ctor_get(v___x_3398_, 1);
v_ngen_3402_ = lean_ctor_get(v___x_3398_, 2);
v_auxDeclNGen_3403_ = lean_ctor_get(v___x_3398_, 3);
v_cache_3404_ = lean_ctor_get(v___x_3398_, 5);
v_recordedDeps_3405_ = lean_ctor_get(v___x_3398_, 6);
v_messages_3406_ = lean_ctor_get(v___x_3398_, 7);
v_infoState_3407_ = lean_ctor_get(v___x_3398_, 8);
v_snapshotTasks_3408_ = lean_ctor_get(v___x_3398_, 9);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3410_ = v___x_3398_;
v_isShared_3411_ = v_isSharedCheck_3427_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_snapshotTasks_3408_);
lean_inc(v_infoState_3407_);
lean_inc(v_messages_3406_);
lean_inc(v_recordedDeps_3405_);
lean_inc(v_cache_3404_);
lean_inc(v_traceState_3399_);
lean_inc(v_auxDeclNGen_3403_);
lean_inc(v_ngen_3402_);
lean_inc(v_nextMacroScope_3401_);
lean_inc(v_env_3400_);
lean_dec(v___x_3398_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3427_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
uint64_t v_tid_3412_; lean_object* v_traces_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3426_; 
v_tid_3412_ = lean_ctor_get_uint64(v_traceState_3399_, sizeof(void*)*1);
v_traces_3413_ = lean_ctor_get(v_traceState_3399_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_traceState_3399_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3415_ = v_traceState_3399_;
v_isShared_3416_ = v_isSharedCheck_3426_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_traces_3413_);
lean_dec(v_traceState_3399_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3426_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3417_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3350_, v_traces_3413_);
lean_dec_ref(v_traces_3413_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3417_);
v___x_3419_ = v___x_3415_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3417_);
lean_ctor_set_uint64(v_reuseFailAlloc_3425_, sizeof(void*)*1, v_tid_3412_);
v___x_3419_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 4, v___x_3419_);
v___x_3421_ = v___x_3410_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_env_3400_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_nextMacroScope_3401_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_ngen_3402_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_auxDeclNGen_3403_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3424_, 5, v_cache_3404_);
lean_ctor_set(v_reuseFailAlloc_3424_, 6, v_recordedDeps_3405_);
lean_ctor_set(v_reuseFailAlloc_3424_, 7, v_messages_3406_);
lean_ctor_set(v_reuseFailAlloc_3424_, 8, v_infoState_3407_);
lean_ctor_set(v_reuseFailAlloc_3424_, 9, v_snapshotTasks_3408_);
v___x_3421_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_st_ref_put(v___y_3358_, v___x_3421_);
v___x_3423_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3360_);
return v___x_3423_;
}
}
}
}
}
else
{
goto v___jp_3391_;
}
}
else
{
goto v___jp_3391_;
}
}
v___jp_3428_:
{
double v___x_3430_; double v___x_3431_; double v___x_3432_; uint8_t v___x_3433_; 
v___x_3430_ = lean_unbox_float(v_snd_3377_);
v___x_3431_ = lean_unbox_float(v_fst_3376_);
v___x_3432_ = lean_float_sub(v___x_3430_, v___x_3431_);
v___x_3433_ = lean_float_decLt(v___y_3429_, v___x_3432_);
v___y_3397_ = v___x_3433_;
goto v___jp_3396_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3345_ = stack[0].m_obj;
uint8_t v_collapsed_3346_ = stack[1].m_num;
lean_object* v_tag_3347_ = stack[2].m_obj;
lean_object* v_opts_3348_ = stack[3].m_obj;
uint8_t v_clsEnabled_3349_ = stack[4].m_num;
lean_object* v_oldTraces_3350_ = stack[5].m_obj;
lean_object* v_msg_3351_ = stack[6].m_obj;
lean_object* v_resStartStop_3352_ = stack[7].m_obj;
lean_object* v___y_3353_ = stack[8].m_obj;
lean_object* v___y_3354_ = stack[9].m_obj;
lean_object* v___y_3355_ = stack[10].m_obj;
lean_object* v___y_3356_ = stack[11].m_obj;
lean_object* v___y_3357_ = stack[12].m_obj;
lean_object* v___y_3358_ = stack[13].m_obj;
lean_object* v_res_3444_;
v_res_3444_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3345_, v_collapsed_3346_, v_tag_3347_, v_opts_3348_, v_clsEnabled_3349_, v_oldTraces_3350_, v_msg_3351_, v_resStartStop_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
stack->m_obj
 = v_res_3444_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3445_, lean_object* v_collapsed_3446_, lean_object* v_tag_3447_, lean_object* v_opts_3448_, lean_object* v_clsEnabled_3449_, lean_object* v_oldTraces_3450_, lean_object* v_msg_3451_, lean_object* v_resStartStop_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
uint8_t v_collapsed_boxed_3460_; uint8_t v_clsEnabled_boxed_3461_; lean_object* v_res_3462_; 
v_collapsed_boxed_3460_ = lean_unbox(v_collapsed_3446_);
v_clsEnabled_boxed_3461_ = lean_unbox(v_clsEnabled_3449_);
v_res_3462_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3445_, v_collapsed_boxed_3460_, v_tag_3447_, v_opts_3448_, v_clsEnabled_boxed_3461_, v_oldTraces_3450_, v_msg_3451_, v_resStartStop_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v_opts_3448_);
return v_res_3462_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_unsigned_to_nat(32u);
v___x_3464_ = lean_mk_empty_array_with_capacity(v___x_3463_);
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
return v___x_3465_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3466_ = ((size_t)5ULL);
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = lean_unsigned_to_nat(32u);
v___x_3469_ = lean_mk_empty_array_with_capacity(v___x_3468_);
v___x_3470_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3471_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v___x_3469_);
lean_ctor_set(v___x_3471_, 2, v___x_3467_);
lean_ctor_set(v___x_3471_, 3, v___x_3467_);
lean_ctor_set_usize(v___x_3471_, 4, v___x_3466_);
return v___x_3471_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3472_){
_start:
{
lean_object* v___x_3474_; lean_object* v_traceState_3475_; lean_object* v_traces_3476_; lean_object* v___x_3477_; lean_object* v_traceState_3478_; lean_object* v_env_3479_; lean_object* v_nextMacroScope_3480_; lean_object* v_ngen_3481_; lean_object* v_auxDeclNGen_3482_; lean_object* v_cache_3483_; lean_object* v_recordedDeps_3484_; lean_object* v_messages_3485_; lean_object* v_infoState_3486_; lean_object* v_snapshotTasks_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3506_; 
v___x_3474_ = lean_st_ref_get(v___y_3472_);
v_traceState_3475_ = lean_ctor_get(v___x_3474_, 4);
lean_inc_ref(v_traceState_3475_);
lean_dec(v___x_3474_);
v_traces_3476_ = lean_ctor_get(v_traceState_3475_, 0);
lean_inc_ref(v_traces_3476_);
lean_dec_ref(v_traceState_3475_);
v___x_3477_ = lean_st_ref_take(v___y_3472_);
v_traceState_3478_ = lean_ctor_get(v___x_3477_, 4);
v_env_3479_ = lean_ctor_get(v___x_3477_, 0);
v_nextMacroScope_3480_ = lean_ctor_get(v___x_3477_, 1);
v_ngen_3481_ = lean_ctor_get(v___x_3477_, 2);
v_auxDeclNGen_3482_ = lean_ctor_get(v___x_3477_, 3);
v_cache_3483_ = lean_ctor_get(v___x_3477_, 5);
v_recordedDeps_3484_ = lean_ctor_get(v___x_3477_, 6);
v_messages_3485_ = lean_ctor_get(v___x_3477_, 7);
v_infoState_3486_ = lean_ctor_get(v___x_3477_, 8);
v_snapshotTasks_3487_ = lean_ctor_get(v___x_3477_, 9);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3489_ = v___x_3477_;
v_isShared_3490_ = v_isSharedCheck_3506_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_snapshotTasks_3487_);
lean_inc(v_infoState_3486_);
lean_inc(v_messages_3485_);
lean_inc(v_recordedDeps_3484_);
lean_inc(v_cache_3483_);
lean_inc(v_traceState_3478_);
lean_inc(v_auxDeclNGen_3482_);
lean_inc(v_ngen_3481_);
lean_inc(v_nextMacroScope_3480_);
lean_inc(v_env_3479_);
lean_dec(v___x_3477_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3506_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
uint64_t v_tid_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3504_; 
v_tid_3491_ = lean_ctor_get_uint64(v_traceState_3478_, sizeof(void*)*1);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_traceState_3478_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; 
v_unused_3505_ = lean_ctor_get(v_traceState_3478_, 0);
lean_dec(v_unused_3505_);
v___x_3493_ = v_traceState_3478_;
v_isShared_3494_ = v_isSharedCheck_3504_;
goto v_resetjp_3492_;
}
else
{
lean_dec(v_traceState_3478_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3504_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3495_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3495_);
lean_ctor_set_uint64(v_reuseFailAlloc_3503_, sizeof(void*)*1, v_tid_3491_);
v___x_3497_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 4, v___x_3497_);
v___x_3499_ = v___x_3489_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_env_3479_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_nextMacroScope_3480_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_ngen_3481_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_auxDeclNGen_3482_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3502_, 5, v_cache_3483_);
lean_ctor_set(v_reuseFailAlloc_3502_, 6, v_recordedDeps_3484_);
lean_ctor_set(v_reuseFailAlloc_3502_, 7, v_messages_3485_);
lean_ctor_set(v_reuseFailAlloc_3502_, 8, v_infoState_3486_);
lean_ctor_set(v_reuseFailAlloc_3502_, 9, v_snapshotTasks_3487_);
v___x_3499_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_st_ref_put(v___y_3472_, v___x_3499_);
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_traces_3476_);
return v___x_3501_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3472_ = stack[0].m_obj;
lean_object* v_res_3507_;
v_res_3507_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3472_);
stack->m_obj
 = v_res_3507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3508_);
lean_dec(v___y_3508_);
return v_res_3510_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; 
lean_inc(v___y_3513_);
lean_inc(v___y_3512_);
v___x_3519_ = lean_apply_7(v_x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, lean_box(0));
return v___x_3519_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3511_ = stack[0].m_obj;
lean_object* v___y_3512_ = stack[1].m_obj;
lean_object* v___y_3513_ = stack[2].m_obj;
lean_object* v___y_3514_ = stack[3].m_obj;
lean_object* v___y_3515_ = stack[4].m_obj;
lean_object* v___y_3516_ = stack[5].m_obj;
lean_object* v___y_3517_ = stack[6].m_obj;
lean_object* v_res_3520_;
v_res_3520_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
stack->m_obj
 = v_res_3520_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3523_);
lean_dec(v___y_3522_);
return v_res_3529_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3530_, lean_object* v_localInsts_3531_, lean_object* v_x_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___f_3540_; lean_object* v___x_3541_; 
lean_inc(v___y_3534_);
lean_inc(v___y_3533_);
v___f_3540_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3540_, 0, v_x_3532_);
lean_closure_set(v___f_3540_, 1, v___y_3533_);
lean_closure_set(v___f_3540_, 2, v___y_3534_);
v___x_3541_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3530_, v_localInsts_3531_, v___f_3540_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3541_) == 0)
{
return v___x_3541_;
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3541_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3530_ = stack[0].m_obj;
lean_object* v_localInsts_3531_ = stack[1].m_obj;
lean_object* v_x_3532_ = stack[2].m_obj;
lean_object* v___y_3533_ = stack[3].m_obj;
lean_object* v___y_3534_ = stack[4].m_obj;
lean_object* v___y_3535_ = stack[5].m_obj;
lean_object* v___y_3536_ = stack[6].m_obj;
lean_object* v___y_3537_ = stack[7].m_obj;
lean_object* v___y_3538_ = stack[8].m_obj;
lean_object* v_res_3550_;
v_res_3550_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3530_, v_localInsts_3531_, v_x_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
stack->m_obj
 = v_res_3550_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3551_, lean_object* v_localInsts_3552_, lean_object* v_x_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3551_, v_localInsts_3552_, v_x_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec(v___y_3554_);
return v_res_3561_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v_ngen_3565_; lean_object* v_namePrefix_3566_; lean_object* v_idx_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3597_; 
v___x_3564_ = lean_st_ref_get(v___y_3562_);
v_ngen_3565_ = lean_ctor_get(v___x_3564_, 2);
lean_inc_ref(v_ngen_3565_);
lean_dec(v___x_3564_);
v_namePrefix_3566_ = lean_ctor_get(v_ngen_3565_, 0);
v_idx_3567_ = lean_ctor_get(v_ngen_3565_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_ngen_3565_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3569_ = v_ngen_3565_;
v_isShared_3570_ = v_isSharedCheck_3597_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_idx_3567_);
lean_inc(v_namePrefix_3566_);
lean_dec(v_ngen_3565_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3597_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v_r_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
lean_inc(v_idx_3567_);
lean_inc(v_namePrefix_3566_);
v_r_3571_ = l_Lean_Name_num___override(v_namePrefix_3566_, v_idx_3567_);
v___x_3572_ = lean_unsigned_to_nat(1u);
v___x_3573_ = lean_nat_add(v_idx_3567_, v___x_3572_);
lean_dec(v_idx_3567_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3573_);
v___x_3575_ = v___x_3569_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_namePrefix_3566_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; lean_object* v_env_3577_; lean_object* v_nextMacroScope_3578_; lean_object* v_auxDeclNGen_3579_; lean_object* v_traceState_3580_; lean_object* v_cache_3581_; lean_object* v_recordedDeps_3582_; lean_object* v_messages_3583_; lean_object* v_infoState_3584_; lean_object* v_snapshotTasks_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3594_; 
v___x_3576_ = lean_st_ref_take(v___y_3562_);
v_env_3577_ = lean_ctor_get(v___x_3576_, 0);
v_nextMacroScope_3578_ = lean_ctor_get(v___x_3576_, 1);
v_auxDeclNGen_3579_ = lean_ctor_get(v___x_3576_, 3);
v_traceState_3580_ = lean_ctor_get(v___x_3576_, 4);
v_cache_3581_ = lean_ctor_get(v___x_3576_, 5);
v_recordedDeps_3582_ = lean_ctor_get(v___x_3576_, 6);
v_messages_3583_ = lean_ctor_get(v___x_3576_, 7);
v_infoState_3584_ = lean_ctor_get(v___x_3576_, 8);
v_snapshotTasks_3585_ = lean_ctor_get(v___x_3576_, 9);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v___x_3576_, 2);
lean_dec(v_unused_3595_);
v___x_3587_ = v___x_3576_;
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_snapshotTasks_3585_);
lean_inc(v_infoState_3584_);
lean_inc(v_messages_3583_);
lean_inc(v_recordedDeps_3582_);
lean_inc(v_cache_3581_);
lean_inc(v_traceState_3580_);
lean_inc(v_auxDeclNGen_3579_);
lean_inc(v_nextMacroScope_3578_);
lean_inc(v_env_3577_);
lean_dec(v___x_3576_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 2, v___x_3575_);
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_env_3577_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_nextMacroScope_3578_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_auxDeclNGen_3579_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v_traceState_3580_);
lean_ctor_set(v_reuseFailAlloc_3593_, 5, v_cache_3581_);
lean_ctor_set(v_reuseFailAlloc_3593_, 6, v_recordedDeps_3582_);
lean_ctor_set(v_reuseFailAlloc_3593_, 7, v_messages_3583_);
lean_ctor_set(v_reuseFailAlloc_3593_, 8, v_infoState_3584_);
lean_ctor_set(v_reuseFailAlloc_3593_, 9, v_snapshotTasks_3585_);
v___x_3590_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_st_ref_put(v___y_3562_, v___x_3590_);
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v_r_3571_);
return v___x_3592_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3562_ = stack[0].m_obj;
lean_object* v_res_3598_;
v_res_3598_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3562_);
stack->m_obj
 = v_res_3598_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3599_);
lean_dec(v___y_3599_);
return v_res_3601_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
v___x_3609_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3607_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3602_ = stack[0].m_obj;
lean_object* v___y_3603_ = stack[1].m_obj;
lean_object* v___y_3604_ = stack[2].m_obj;
lean_object* v___y_3605_ = stack[3].m_obj;
lean_object* v___y_3606_ = stack[4].m_obj;
lean_object* v___y_3607_ = stack[5].m_obj;
lean_object* v_res_3618_;
v_res_3618_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
stack->m_obj
 = v_res_3618_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec(v___y_3619_);
return v_res_3626_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3629_ = l_Lean_stringToMessageData(v___x_3628_);
return v___x_3629_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3632_ = l_Lean_stringToMessageData(v___x_3631_);
return v___x_3632_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3635_, lean_object* v_x_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; lean_object* v___y_3646_; uint8_t v___x_3655_; 
v___x_3644_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3655_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3637_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; 
v___x_3656_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3646_ = v___x_3656_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3657_; 
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3646_ = v___x_3657_;
goto v___jp_3645_;
}
v___jp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_inc_ref(v___y_3646_);
v___x_3647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___y_3646_);
v___x_3648_ = l_Lean_MessageData_ofFormat(v___x_3647_);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3644_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = l_Lean_indentExpr(v_e_3635_);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3635_ = stack[0].m_obj;
lean_object* v_x_3636_ = stack[1].m_obj;
lean_object* v___y_3637_ = stack[2].m_obj;
lean_object* v___y_3638_ = stack[3].m_obj;
lean_object* v___y_3639_ = stack[4].m_obj;
lean_object* v___y_3640_ = stack[5].m_obj;
lean_object* v___y_3641_ = stack[6].m_obj;
lean_object* v___y_3642_ = stack[7].m_obj;
lean_object* v_res_3658_;
v_res_3658_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3635_, v_x_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
stack->m_obj
 = v_res_3658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3659_, lean_object* v_x_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3659_, v_x_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v_x_3660_);
return v_res_3668_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3669_, lean_object* v_x_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_keyedConfig_3678_; uint8_t v_trackZetaDelta_3679_; lean_object* v_zetaDeltaSet_3680_; lean_object* v_localInstances_3681_; lean_object* v_defEqCtx_x3f_3682_; lean_object* v_synthPendingDepth_3683_; lean_object* v_customCanUnfoldPredicate_x3f_3684_; uint8_t v_univApprox_3685_; uint8_t v_inTypeClassResolution_3686_; uint8_t v_cacheInferType_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_keyedConfig_3678_ = lean_ctor_get(v___y_3673_, 0);
v_trackZetaDelta_3679_ = lean_ctor_get_uint8(v___y_3673_, sizeof(void*)*7);
v_zetaDeltaSet_3680_ = lean_ctor_get(v___y_3673_, 1);
v_localInstances_3681_ = lean_ctor_get(v___y_3673_, 3);
v_defEqCtx_x3f_3682_ = lean_ctor_get(v___y_3673_, 4);
v_synthPendingDepth_3683_ = lean_ctor_get(v___y_3673_, 5);
v_customCanUnfoldPredicate_x3f_3684_ = lean_ctor_get(v___y_3673_, 6);
v_univApprox_3685_ = lean_ctor_get_uint8(v___y_3673_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3686_ = lean_ctor_get_uint8(v___y_3673_, sizeof(void*)*7 + 2);
v_cacheInferType_3687_ = lean_ctor_get_uint8(v___y_3673_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3684_);
lean_inc(v_synthPendingDepth_3683_);
lean_inc(v_defEqCtx_x3f_3682_);
lean_inc_ref(v_localInstances_3681_);
lean_inc(v_zetaDeltaSet_3680_);
lean_inc_ref(v_keyedConfig_3678_);
v___x_3688_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3688_, 0, v_keyedConfig_3678_);
lean_ctor_set(v___x_3688_, 1, v_zetaDeltaSet_3680_);
lean_ctor_set(v___x_3688_, 2, v_lctx_3669_);
lean_ctor_set(v___x_3688_, 3, v_localInstances_3681_);
lean_ctor_set(v___x_3688_, 4, v_defEqCtx_x3f_3682_);
lean_ctor_set(v___x_3688_, 5, v_synthPendingDepth_3683_);
lean_ctor_set(v___x_3688_, 6, v_customCanUnfoldPredicate_x3f_3684_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7, v_trackZetaDelta_3679_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7 + 1, v_univApprox_3685_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3686_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7 + 3, v_cacheInferType_3687_);
lean_inc(v___y_3676_);
lean_inc_ref(v___y_3675_);
lean_inc(v___y_3674_);
lean_inc(v___y_3672_);
lean_inc(v___y_3671_);
v___x_3689_ = lean_apply_7(v_x_3670_, v___y_3671_, v___y_3672_, v___x_3688_, v___y_3674_, v___y_3675_, v___y_3676_, lean_box(0));
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
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
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
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
else
{
return v___x_3689_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3669_ = stack[0].m_obj;
lean_object* v_x_3670_ = stack[1].m_obj;
lean_object* v___y_3671_ = stack[2].m_obj;
lean_object* v___y_3672_ = stack[3].m_obj;
lean_object* v___y_3673_ = stack[4].m_obj;
lean_object* v___y_3674_ = stack[5].m_obj;
lean_object* v___y_3675_ = stack[6].m_obj;
lean_object* v___y_3676_ = stack[7].m_obj;
lean_object* v_res_3698_;
v_res_3698_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3669_, v_x_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
stack->m_obj
 = v_res_3698_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3699_, lean_object* v_x_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3699_, v_x_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec(v___y_3701_);
return v_res_3708_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3711_, lean_object* v_letFVars_3712_, lean_object* v_lctx_3713_, lean_object* v_v_3714_, lean_object* v_e_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3723_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3724_ = lean_expr_instantiate_rev(v_e_3715_, v_fvars_3711_);
v___x_3725_ = lean_apply_1(v_v_3714_, v___x_3724_);
v___x_3726_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3726_, 0, lean_box(0));
lean_closure_set(v___x_3726_, 1, v_letFVars_3712_);
lean_closure_set(v___x_3726_, 2, v___x_3725_);
v___x_3727_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3713_, v___x_3723_, v___x_3726_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
return v___x_3727_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3711_ = stack[0].m_obj;
lean_object* v_letFVars_3712_ = stack[1].m_obj;
lean_object* v_lctx_3713_ = stack[2].m_obj;
lean_object* v_v_3714_ = stack[3].m_obj;
lean_object* v_e_3715_ = stack[4].m_obj;
lean_object* v___y_3716_ = stack[5].m_obj;
lean_object* v___y_3717_ = stack[6].m_obj;
lean_object* v___y_3718_ = stack[7].m_obj;
lean_object* v___y_3719_ = stack[8].m_obj;
lean_object* v___y_3720_ = stack[9].m_obj;
lean_object* v___y_3721_ = stack[10].m_obj;
lean_object* v_res_3728_;
v_res_3728_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3711_, v_letFVars_3712_, v_lctx_3713_, v_v_3714_, v_e_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
stack->m_obj
 = v_res_3728_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3729_, lean_object* v_letFVars_3730_, lean_object* v_lctx_3731_, lean_object* v_v_3732_, lean_object* v_e_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3729_, v_letFVars_3730_, v_lctx_3731_, v_v_3732_, v_e_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v_e_3733_);
lean_dec_ref(v_fvars_3729_);
return v_res_3741_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3744_ = l_Lean_stringToMessageData(v___x_3743_);
return v___x_3744_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
lean_inc_ref(v_a_3745_);
v___x_3754_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3745_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v_expr_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3806_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v_expr_3756_ = lean_ctor_get(v_a_3746_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_a_3746_);
if (v_isSharedCheck_3806_ == 0)
{
lean_object* v_unused_3807_; 
v_unused_3807_ = lean_ctor_get(v_a_3746_, 1);
lean_dec(v_unused_3807_);
v___x_3758_ = v_a_3746_;
v_isShared_3759_ = v_isSharedCheck_3806_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_expr_3756_);
lean_dec(v_a_3746_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3806_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; 
lean_inc(v_a_3755_);
lean_inc_ref(v_expr_3756_);
v___x_3760_ = l_Lean_Meta_isExprDefEq(v_expr_3756_, v_a_3755_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3797_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3797_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3797_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
uint8_t v___x_3765_; 
v___x_3765_ = lean_unbox(v_a_3761_);
lean_dec(v_a_3761_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_del_object(v___x_3763_);
v___x_3766_ = lean_box(0);
v___x_3767_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3768_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3755_, v_expr_3756_, v___x_3766_, v___x_3767_, v___y_3749_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v_expr_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3783_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___x_3768_, 1);
v_expr_3770_ = lean_ctor_get(v_a_3745_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_a_3745_);
if (v_isSharedCheck_3783_ == 0)
{
lean_object* v_unused_3784_; 
v_unused_3784_ = lean_ctor_get(v_a_3745_, 1);
lean_dec(v_unused_3784_);
v___x_3772_ = v_a_3745_;
v_isShared_3773_ = v_isSharedCheck_3783_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_expr_3770_);
lean_dec(v_a_3745_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3783_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3774_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3775_ = l_Lean_indentExpr(v_expr_3770_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 7);
lean_ctor_set(v___x_3772_, 1, v___x_3775_);
lean_ctor_set(v___x_3772_, 0, v___x_3774_);
v___x_3777_ = v___x_3772_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v___x_3775_);
v___x_3777_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 7);
lean_ctor_set(v___x_3758_, 1, v_a_3769_);
lean_ctor_set(v___x_3758_, 0, v___x_3777_);
v___x_3779_ = v___x_3758_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_a_3769_);
v___x_3779_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3779_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_del_object(v___x_3758_);
lean_dec_ref(v_a_3745_);
v_a_3785_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3768_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3768_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_del_object(v___x_3758_);
lean_dec_ref(v_expr_3756_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3745_);
v___x_3793_ = lean_box(0);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3793_);
v___x_3795_ = v___x_3763_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_del_object(v___x_3758_);
lean_dec_ref(v_expr_3756_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3745_);
v_a_3798_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3760_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3760_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v_a_3746_);
lean_dec_ref(v_a_3745_);
v_a_3808_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3754_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3754_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3745_ = stack[0].m_obj;
lean_object* v_a_3746_ = stack[1].m_obj;
lean_object* v___y_3747_ = stack[2].m_obj;
lean_object* v___y_3748_ = stack[3].m_obj;
lean_object* v___y_3749_ = stack[4].m_obj;
lean_object* v___y_3750_ = stack[5].m_obj;
lean_object* v___y_3751_ = stack[6].m_obj;
lean_object* v___y_3752_ = stack[7].m_obj;
lean_object* v_res_3816_;
v_res_3816_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3745_, v_a_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
stack->m_obj
 = v_res_3816_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3817_, v_a_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec(v___y_3819_);
return v_res_3826_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3828_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3829_ = l_Lean_stringToMessageData(v___x_3828_);
return v___x_3829_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
if (lean_obj_tag(v_e_3830_) == 5)
{
lean_object* v_fn_3838_; lean_object* v_arg_3839_; lean_object* v___x_3840_; 
v_fn_3838_ = lean_ctor_get(v_e_3830_, 0);
v_arg_3839_ = lean_ctor_get(v_e_3830_, 1);
lean_inc_ref(v_fn_3838_);
v___x_3840_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3838_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
lean_inc_ref(v_arg_3839_);
v___x_3842_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3839_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3865_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3865_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3865_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_expr_3847_; size_t v___x_3848_; size_t v___x_3849_; uint8_t v___x_3850_; 
v_expr_3847_ = lean_ctor_get(v_a_3843_, 0);
lean_inc_ref(v_expr_3847_);
lean_dec(v_a_3843_);
v___x_3848_ = lean_ptr_addr(v_fn_3838_);
v___x_3849_ = lean_ptr_addr(v_a_3841_);
v___x_3850_ = lean_usize_dec_eq(v___x_3848_, v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
lean_dec_ref_known(v_e_3830_, 2);
v___x_3851_ = l_Lean_Expr_app___override(v_a_3841_, v_expr_3847_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3851_);
v___x_3853_ = v___x_3845_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
else
{
size_t v___x_3855_; size_t v___x_3856_; uint8_t v___x_3857_; 
v___x_3855_ = lean_ptr_addr(v_arg_3839_);
v___x_3856_ = lean_ptr_addr(v_expr_3847_);
v___x_3857_ = lean_usize_dec_eq(v___x_3855_, v___x_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
lean_dec_ref_known(v_e_3830_, 2);
v___x_3858_ = l_Lean_Expr_app___override(v_a_3841_, v_expr_3847_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3858_);
v___x_3860_ = v___x_3845_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
else
{
lean_object* v___x_3863_; 
lean_dec_ref(v_expr_3847_);
lean_dec(v_a_3841_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v_e_3830_);
v___x_3863_ = v___x_3845_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_e_3830_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_a_3841_);
lean_dec_ref_known(v_e_3830_, 2);
v_a_3866_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3842_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3842_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3830_, 2);
return v___x_3840_;
}
}
else
{
lean_object* v___x_3874_; 
v___x_3874_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3883_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v_expr_3879_; lean_object* v___x_3881_; 
v_expr_3879_ = lean_ctor_get(v_a_3875_, 0);
lean_inc_ref(v_expr_3879_);
lean_dec(v_a_3875_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v_expr_3879_);
v___x_3881_ = v___x_3877_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_expr_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
v_a_3884_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3874_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3874_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3830_ = stack[0].m_obj;
lean_object* v_a_3831_ = stack[1].m_obj;
lean_object* v_a_3832_ = stack[2].m_obj;
lean_object* v_a_3833_ = stack[3].m_obj;
lean_object* v_a_3834_ = stack[4].m_obj;
lean_object* v_a_3835_ = stack[5].m_obj;
lean_object* v_a_3836_ = stack[6].m_obj;
lean_object* v_res_3892_;
v_res_3892_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
stack->m_obj
 = v_res_3892_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
lean_dec(v_a_3895_);
lean_dec(v_a_3894_);
return v_res_3901_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_){
_start:
{
if (lean_obj_tag(v_e_3902_) == 5)
{
lean_object* v_fn_3910_; lean_object* v_arg_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_fn_3910_ = lean_ctor_get(v_e_3902_, 0);
v_arg_3911_ = lean_ctor_get(v_e_3902_, 1);
lean_inc_ref_n(v_fn_3910_, 2);
v___x_3912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3912_, 0, v_fn_3910_);
v___x_3913_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3910_, v___x_3912_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
lean_inc_ref(v_arg_3911_);
v___x_3915_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3911_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3902_, v_a_3914_, v_a_3916_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
return v___x_3917_;
}
else
{
lean_dec(v_a_3914_);
lean_dec_ref_known(v_e_3902_, 2);
return v___x_3915_;
}
}
else
{
lean_dec_ref_known(v_e_3902_, 2);
return v___x_3913_;
}
}
else
{
lean_object* v___x_3918_; 
v___x_3918_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
return v___x_3918_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3902_ = stack[0].m_obj;
lean_object* v_a_3903_ = stack[1].m_obj;
lean_object* v_a_3904_ = stack[2].m_obj;
lean_object* v_a_3905_ = stack[3].m_obj;
lean_object* v_a_3906_ = stack[4].m_obj;
lean_object* v_a_3907_ = stack[5].m_obj;
lean_object* v_a_3908_ = stack[6].m_obj;
lean_object* v_res_3919_;
v_res_3919_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
stack->m_obj
 = v_res_3919_;
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
uint8_t v___x_3928_; 
v___x_3928_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3921_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
v___x_3929_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3939_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3939_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3939_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3934_ = lean_box(0);
v___x_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3935_, 0, v_a_3930_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3935_);
v___x_3937_ = v___x_3932_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_a_3940_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3929_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3929_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_Expr_getAppFn(v_e_3920_);
if (lean_obj_tag(v___x_3948_) == 2)
{
lean_object* v_mvarId_3949_; lean_object* v_dummy_3950_; lean_object* v_nargs_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_mvarId_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_mvarId_3949_);
lean_dec_ref_known(v___x_3948_, 1);
v_dummy_3950_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3951_ = l_Lean_Expr_getAppNumArgs(v_e_3920_);
lean_inc(v_nargs_3951_);
v___x_3952_ = lean_mk_array(v_nargs_3951_, v_dummy_3950_);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = lean_nat_sub(v_nargs_3951_, v___x_3953_);
lean_dec(v_nargs_3951_);
lean_inc_ref(v_e_3920_);
v___x_3955_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3920_, v___x_3952_, v___x_3954_);
v___x_3956_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3949_, v___x_3955_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec(v_mvarId_3949_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v___x_3957_; 
lean_dec_ref_known(v___x_3956_, 1);
v___x_3957_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_3957_;
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec_ref(v_e_3920_);
v_a_3958_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3956_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3956_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
else
{
lean_object* v___x_3966_; 
lean_dec_ref(v___x_3948_);
v___x_3966_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_3966_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3920_ = stack[0].m_obj;
lean_object* v_a_3921_ = stack[1].m_obj;
lean_object* v_a_3922_ = stack[2].m_obj;
lean_object* v_a_3923_ = stack[3].m_obj;
lean_object* v_a_3924_ = stack[4].m_obj;
lean_object* v_a_3925_ = stack[5].m_obj;
lean_object* v_a_3926_ = stack[6].m_obj;
lean_object* v_res_3967_;
v_res_3967_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
stack->m_obj
 = v_res_3967_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec(v_a_3969_);
return v_res_3976_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3987_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v___x_3987_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3986_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_3987_;
}
else
{
return v___x_3985_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3977_ = stack[0].m_obj;
lean_object* v_a_3978_ = stack[1].m_obj;
lean_object* v_a_3979_ = stack[2].m_obj;
lean_object* v_a_3980_ = stack[3].m_obj;
lean_object* v_a_3981_ = stack[4].m_obj;
lean_object* v_a_3982_ = stack[5].m_obj;
lean_object* v_a_3983_ = stack[6].m_obj;
lean_object* v_res_3988_;
v_res_3988_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
stack->m_obj
 = v_res_3988_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec(v_a_3990_);
return v_res_3997_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3998_, lean_object* v_fvars_3999_, lean_object* v_doms_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3998_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3999_, v_doms_4000_, v_a_4009_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
return v___x_4010_;
}
else
{
return v___x_4008_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3998_ = stack[0].m_obj;
lean_object* v_fvars_3999_ = stack[1].m_obj;
lean_object* v_doms_4000_ = stack[2].m_obj;
lean_object* v___y_4001_ = stack[3].m_obj;
lean_object* v___y_4002_ = stack[4].m_obj;
lean_object* v___y_4003_ = stack[5].m_obj;
lean_object* v___y_4004_ = stack[6].m_obj;
lean_object* v___y_4005_ = stack[7].m_obj;
lean_object* v___y_4006_ = stack[8].m_obj;
lean_object* v_res_4011_;
v_res_4011_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3998_, v_fvars_3999_, v_doms_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
stack->m_obj
 = v_res_4011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_4012_, lean_object* v_fvars_4013_, lean_object* v_doms_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_4012_, v_fvars_4013_, v_doms_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v_doms_4014_);
lean_dec_ref(v_fvars_4013_);
return v_res_4022_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_4023_, lean_object* v_fvars_4024_, lean_object* v_doms_4025_, lean_object* v_e_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_4026_, v_a_4028_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
if (lean_obj_tag(v_a_4035_) == 1)
{
lean_object* v_val_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec_ref(v_e_4026_);
v_val_4036_ = lean_ctor_get(v_a_4035_, 0);
lean_inc(v_val_4036_);
lean_dec_ref_known(v_a_4035_, 1);
v___x_4037_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_4038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_4038_, 0, v_fvars_4024_);
lean_closure_set(v___x_4038_, 1, v_doms_4025_);
lean_closure_set(v___x_4038_, 2, v_val_4036_);
v___x_4039_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4023_, v___x_4037_, v___x_4038_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
return v___x_4039_;
}
else
{
lean_dec(v_a_4035_);
if (lean_obj_tag(v_e_4026_) == 7)
{
lean_object* v_binderName_4040_; lean_object* v_binderType_4041_; lean_object* v_body_4042_; uint8_t v_binderInfo_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v_binderName_4040_ = lean_ctor_get(v_e_4026_, 0);
lean_inc(v_binderName_4040_);
v_binderType_4041_ = lean_ctor_get(v_e_4026_, 1);
lean_inc_ref(v_binderType_4041_);
v_body_4042_ = lean_ctor_get(v_e_4026_, 2);
lean_inc_ref(v_body_4042_);
v_binderInfo_4043_ = lean_ctor_get_uint8(v_e_4026_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4026_, 3);
v___x_4044_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_4045_ = lean_expr_instantiate_rev(v_binderType_4041_, v_fvars_4024_);
lean_dec_ref(v_binderType_4041_);
v___x_4046_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_4046_, 0, v___x_4045_);
lean_inc_ref(v_lctx_4023_);
v___x_4047_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4023_, v___x_4044_, v___x_4046_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4049_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 1);
v___x_4049_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v_expr_4051_; uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc_n(v_a_4050_, 2);
lean_dec_ref_known(v___x_4049_, 1);
v_expr_4051_ = lean_ctor_get(v_a_4048_, 0);
v___x_4052_ = 0;
lean_inc_ref(v_expr_4051_);
v___x_4053_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4023_, v_a_4050_, v_binderName_4040_, v_expr_4051_, v_binderInfo_4043_, v___x_4052_);
v___x_4054_ = l_Lean_Expr_fvar___override(v_a_4050_);
v___x_4055_ = lean_array_push(v_fvars_4024_, v___x_4054_);
v___x_4056_ = lean_array_push(v_doms_4025_, v_a_4048_);
v_lctx_4023_ = v___x_4053_;
v_fvars_4024_ = v___x_4055_;
v_doms_4025_ = v___x_4056_;
v_e_4026_ = v_body_4042_;
goto _start;
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_dec(v_a_4048_);
lean_dec_ref(v_body_4042_);
lean_dec(v_binderName_4040_);
lean_dec_ref(v_doms_4025_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
v_a_4058_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4049_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4049_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
else
{
lean_dec_ref(v_body_4042_);
lean_dec(v_binderName_4040_);
lean_dec_ref(v_doms_4025_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
return v___x_4047_;
}
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___f_4068_; lean_object* v___x_4069_; 
v___x_4066_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_4067_ = lean_expr_instantiate_rev(v_e_4026_, v_fvars_4024_);
lean_dec_ref(v_e_4026_);
v___f_4068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4068_, 0, v___x_4067_);
lean_closure_set(v___f_4068_, 1, v_fvars_4024_);
lean_closure_set(v___f_4068_, 2, v_doms_4025_);
v___x_4069_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4023_, v___x_4066_, v___f_4068_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
return v___x_4069_;
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_e_4026_);
lean_dec_ref(v_doms_4025_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
v_a_4070_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4034_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4034_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_4023_ = stack[0].m_obj;
lean_object* v_fvars_4024_ = stack[1].m_obj;
lean_object* v_doms_4025_ = stack[2].m_obj;
lean_object* v_e_4026_ = stack[3].m_obj;
lean_object* v_a_4027_ = stack[4].m_obj;
lean_object* v_a_4028_ = stack[5].m_obj;
lean_object* v_a_4029_ = stack[6].m_obj;
lean_object* v_a_4030_ = stack[7].m_obj;
lean_object* v_a_4031_ = stack[8].m_obj;
lean_object* v_a_4032_ = stack[9].m_obj;
lean_object* v_res_4078_;
v_res_4078_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4023_, v_fvars_4024_, v_doms_4025_, v_e_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
stack->m_obj
 = v_res_4078_;
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
uint32_t v___x_4087_; uint8_t v___x_4088_; 
v___x_4087_ = 5;
v___x_4088_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4079_, v___x_4087_);
if (v___x_4088_ == 0)
{
lean_object* v_lctx_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v_lctx_4089_ = lean_ctor_get(v_a_4082_, 2);
v___x_4090_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_4089_);
v___x_4091_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4089_, v___x_4090_, v___x_4090_, v_e_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
return v___x_4091_;
}
else
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = lean_box(0);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v_e_4079_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
return v___x_4094_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4079_ = stack[0].m_obj;
lean_object* v_a_4080_ = stack[1].m_obj;
lean_object* v_a_4081_ = stack[2].m_obj;
lean_object* v_a_4082_ = stack[3].m_obj;
lean_object* v_a_4083_ = stack[4].m_obj;
lean_object* v_a_4084_ = stack[5].m_obj;
lean_object* v_a_4085_ = stack[6].m_obj;
lean_object* v_res_4095_;
v_res_4095_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
stack->m_obj
 = v_res_4095_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
lean_dec(v_a_4097_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_4105_, lean_object* v_e_4106_, lean_object* v_typeName_4107_, lean_object* v_idx_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4105_, v_e_4106_, v_typeName_4107_, v_idx_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec(v___y_4109_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
lean_dec(v_a_4123_);
lean_dec_ref(v_a_4122_);
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
lean_dec(v_a_4118_);
return v_res_4125_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4137_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4126_, v_a_4136_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
return v___x_4137_;
}
else
{
lean_dec_ref(v_fvars_4126_);
return v___x_4135_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_4126_ = stack[0].m_obj;
lean_object* v___y_4127_ = stack[1].m_obj;
lean_object* v___y_4128_ = stack[2].m_obj;
lean_object* v___y_4129_ = stack[3].m_obj;
lean_object* v___y_4130_ = stack[4].m_obj;
lean_object* v___y_4131_ = stack[5].m_obj;
lean_object* v___y_4132_ = stack[6].m_obj;
lean_object* v___y_4133_ = stack[7].m_obj;
lean_object* v_res_4138_;
v_res_4138_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
stack->m_obj
 = v_res_4138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec(v___y_4141_);
return v_res_4148_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4149_, lean_object* v_fvars_4150_, lean_object* v_e_4151_, lean_object* v_letFVars_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
switch(lean_obj_tag(v_e_4151_))
{
case 6:
{
lean_object* v_binderName_4160_; lean_object* v_binderType_4161_; lean_object* v_body_4162_; uint8_t v_binderInfo_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_binderName_4160_ = lean_ctor_get(v_e_4151_, 0);
lean_inc(v_binderName_4160_);
v_binderType_4161_ = lean_ctor_get(v_e_4151_, 1);
lean_inc_ref(v_binderType_4161_);
v_body_4162_ = lean_ctor_get(v_e_4151_, 2);
lean_inc_ref(v_body_4162_);
v_binderInfo_4163_ = lean_ctor_get_uint8(v_e_4151_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4151_, 3);
v___x_4164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4149_);
lean_inc(v_letFVars_4152_);
v___x_4165_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4150_, v_letFVars_4152_, v_lctx_4149_, v___x_4164_, v_binderType_4161_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
lean_dec_ref(v_binderType_4161_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4167_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4167_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v_expr_4169_; uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc_n(v_a_4168_, 2);
lean_dec_ref_known(v___x_4167_, 1);
v_expr_4169_ = lean_ctor_get(v_a_4166_, 0);
lean_inc_ref(v_expr_4169_);
lean_dec(v_a_4166_);
v___x_4170_ = 0;
v___x_4171_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4149_, v_a_4168_, v_binderName_4160_, v_expr_4169_, v_binderInfo_4163_, v___x_4170_);
v___x_4172_ = l_Lean_Expr_fvar___override(v_a_4168_);
v___x_4173_ = lean_array_push(v_fvars_4150_, v___x_4172_);
v_lctx_4149_ = v___x_4171_;
v_fvars_4150_ = v___x_4173_;
v_e_4151_ = v_body_4162_;
goto _start;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_a_4166_);
lean_dec_ref(v_body_4162_);
lean_dec(v_binderName_4160_);
lean_dec(v_letFVars_4152_);
lean_dec_ref(v_fvars_4150_);
lean_dec_ref(v_lctx_4149_);
v_a_4175_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4167_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4167_);
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
lean_dec_ref(v_body_4162_);
lean_dec(v_binderName_4160_);
lean_dec(v_letFVars_4152_);
lean_dec_ref(v_fvars_4150_);
lean_dec_ref(v_lctx_4149_);
return v___x_4165_;
}
}
case 8:
{
lean_object* v_declName_4183_; lean_object* v_type_4184_; lean_object* v_value_4185_; lean_object* v_body_4186_; uint8_t v_nondep_4187_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_declName_4183_ = lean_ctor_get(v_e_4151_, 0);
lean_inc(v_declName_4183_);
v_type_4184_ = lean_ctor_get(v_e_4151_, 1);
lean_inc_ref(v_type_4184_);
v_value_4185_ = lean_ctor_get(v_e_4151_, 2);
lean_inc_ref(v_value_4185_);
v_body_4186_ = lean_ctor_get(v_e_4151_, 3);
lean_inc_ref(v_body_4186_);
v_nondep_4187_ = lean_ctor_get_uint8(v_e_4151_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4151_, 4);
v___x_4201_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4149_);
lean_inc(v_letFVars_4152_);
v___x_4202_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4150_, v_letFVars_4152_, v_lctx_4149_, v___x_4201_, v_type_4184_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
lean_dec_ref(v_type_4184_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___x_4204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4149_);
lean_inc(v_letFVars_4152_);
v___x_4205_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4150_, v_letFVars_4152_, v_lctx_4149_, v___x_4204_, v_value_4185_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
lean_dec_ref(v_value_4185_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; uint8_t v___x_4236_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4236_ = l_List_isEmpty___redArg(v_letFVars_4152_);
if (v___x_4236_ == 0)
{
lean_object* v___f_4237_; lean_object* v___x_4238_; 
lean_inc(v_a_4203_);
lean_inc(v_a_4206_);
v___f_4237_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4237_, 0, v_a_4206_);
lean_closure_set(v___f_4237_, 1, v_a_4203_);
lean_inc_ref(v_lctx_4149_);
v___x_4238_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4149_, v___f_4237_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_dec_ref_known(v___x_4238_, 1);
v___y_4208_ = v_a_4153_;
v___y_4209_ = v_a_4154_;
v___y_4210_ = v_a_4155_;
v___y_4211_ = v_a_4156_;
v___y_4212_ = v_a_4157_;
v___y_4213_ = v_a_4158_;
goto v___jp_4207_;
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v_a_4206_);
lean_dec(v_a_4203_);
lean_dec_ref(v_body_4186_);
lean_dec(v_declName_4183_);
lean_dec(v_letFVars_4152_);
lean_dec_ref(v_fvars_4150_);
lean_dec_ref(v_lctx_4149_);
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
v___y_4208_ = v_a_4153_;
v___y_4209_ = v_a_4154_;
v___y_4210_ = v_a_4155_;
v___y_4211_ = v_a_4156_;
v___y_4212_ = v_a_4157_;
v___y_4213_ = v_a_4158_;
goto v___jp_4207_;
}
v___jp_4207_:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v_expr_4216_; lean_object* v_expr_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4226_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v_expr_4216_ = lean_ctor_get(v_a_4203_, 0);
lean_inc_ref(v_expr_4216_);
lean_dec(v_a_4203_);
v_expr_4217_ = lean_ctor_get(v_a_4206_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_a_4206_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; 
v_unused_4227_ = lean_ctor_get(v_a_4206_, 1);
lean_dec(v_unused_4227_);
v___x_4219_ = v_a_4206_;
v_isShared_4220_ = v_isSharedCheck_4226_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_expr_4217_);
lean_dec(v_a_4206_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4226_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
uint8_t v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = 0;
lean_inc(v_a_4215_);
v___x_4222_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4149_, v_a_4215_, v_declName_4183_, v_expr_4216_, v_expr_4217_, v_nondep_4187_, v___x_4221_);
if (v_nondep_4187_ == 0)
{
lean_object* v___x_4224_; 
lean_inc(v_a_4215_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set_tag(v___x_4219_, 1);
lean_ctor_set(v___x_4219_, 1, v_letFVars_4152_);
lean_ctor_set(v___x_4219_, 0, v_a_4215_);
v___x_4224_ = v___x_4219_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4215_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_letFVars_4152_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
v___y_4189_ = v___y_4209_;
v___y_4190_ = v___y_4208_;
v___y_4191_ = v_a_4215_;
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4211_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___x_4222_;
v___y_4196_ = v___y_4213_;
v___y_4197_ = v___x_4224_;
goto v___jp_4188_;
}
}
else
{
lean_del_object(v___x_4219_);
v___y_4189_ = v___y_4209_;
v___y_4190_ = v___y_4208_;
v___y_4191_ = v_a_4215_;
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4211_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___x_4222_;
v___y_4196_ = v___y_4213_;
v___y_4197_ = v_letFVars_4152_;
goto v___jp_4188_;
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec(v_a_4206_);
lean_dec(v_a_4203_);
lean_dec_ref(v_body_4186_);
lean_dec(v_declName_4183_);
lean_dec(v_letFVars_4152_);
lean_dec_ref(v_fvars_4150_);
lean_dec_ref(v_lctx_4149_);
v_a_4228_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4214_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4214_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
}
else
{
lean_dec(v_a_4203_);
lean_dec_ref(v_body_4186_);
lean_dec(v_declName_4183_);
lean_dec(v_letFVars_4152_);
lean_dec_ref(v_fvars_4150_);
lean_dec_ref(v_lctx_4149_);
return v___x_4205_;
}
}
else
{
lean_dec_ref(v_body_4186_);
lean_dec_ref(v_value_4185_);
lean_dec(v_declName_4183_);
lean_dec(v_letFVars_4152_);
lean_dec_ref(v_fvars_4150_);
lean_dec_ref(v_lctx_4149_);
return v___x_4202_;
}
v___jp_4188_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = l_Lean_Expr_fvar___override(v___y_4191_);
v___x_4199_ = lean_array_push(v_fvars_4150_, v___x_4198_);
v_lctx_4149_ = v___y_4195_;
v_fvars_4150_ = v___x_4199_;
v_e_4151_ = v_body_4186_;
v_letFVars_4152_ = v___y_4197_;
v_a_4153_ = v___y_4190_;
v_a_4154_ = v___y_4189_;
v_a_4155_ = v___y_4194_;
v_a_4156_ = v___y_4193_;
v_a_4157_ = v___y_4192_;
v_a_4158_ = v___y_4196_;
goto _start;
}
}
default: 
{
lean_object* v___f_4247_; lean_object* v___x_4248_; 
lean_inc_ref(v_fvars_4150_);
v___f_4247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4247_, 0, v_fvars_4150_);
v___x_4248_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4150_, v_letFVars_4152_, v_lctx_4149_, v___f_4247_, v_e_4151_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
lean_dec_ref(v_e_4151_);
lean_dec_ref(v_fvars_4150_);
return v___x_4248_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_4149_ = stack[0].m_obj;
lean_object* v_fvars_4150_ = stack[1].m_obj;
lean_object* v_e_4151_ = stack[2].m_obj;
lean_object* v_letFVars_4152_ = stack[3].m_obj;
lean_object* v_a_4153_ = stack[4].m_obj;
lean_object* v_a_4154_ = stack[5].m_obj;
lean_object* v_a_4155_ = stack[6].m_obj;
lean_object* v_a_4156_ = stack[7].m_obj;
lean_object* v_a_4157_ = stack[8].m_obj;
lean_object* v_a_4158_ = stack[9].m_obj;
lean_object* v_res_4249_;
v_res_4249_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4149_, v_fvars_4150_, v_e_4151_, v_letFVars_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
stack->m_obj
 = v_res_4249_;
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
uint32_t v___x_4258_; uint8_t v___x_4259_; 
v___x_4258_ = 5;
v___x_4259_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4250_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v_lctx_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_lctx_4260_ = lean_ctor_get(v_a_4253_, 2);
v___x_4261_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4251_);
lean_inc_ref(v_lctx_4260_);
v___x_4262_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4260_, v___x_4261_, v_e_4250_, v_a_4251_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
return v___x_4262_;
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = lean_box(0);
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v_e_4250_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
return v___x_4265_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4250_ = stack[0].m_obj;
lean_object* v_a_4251_ = stack[1].m_obj;
lean_object* v_a_4252_ = stack[2].m_obj;
lean_object* v_a_4253_ = stack[3].m_obj;
lean_object* v_a_4254_ = stack[4].m_obj;
lean_object* v_a_4255_ = stack[5].m_obj;
lean_object* v_a_4256_ = stack[6].m_obj;
lean_object* v_res_4266_;
v_res_4266_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
stack->m_obj
 = v_res_4266_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec(v_a_4268_);
return v_res_4275_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
switch(lean_obj_tag(v_e_4276_))
{
case 0:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4284_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4285_ = l_Lean_MessageData_ofExpr(v_e_4276_);
v___x_4286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4284_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4286_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4287_;
}
case 1:
{
lean_object* v___x_4288_; 
v___x_4288_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4276_, v___y_4279_, v___y_4281_, v___y_4282_);
return v___x_4288_;
}
case 2:
{
lean_object* v___x_4289_; 
v___x_4289_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4289_;
}
case 3:
{
lean_object* v_u_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_u_4290_ = lean_ctor_get(v_e_4276_, 0);
lean_inc(v_u_4290_);
v___x_4291_ = l_Lean_Level_succ___override(v_u_4290_);
v___x_4292_ = l_Lean_Expr_sort___override(v___x_4291_);
v___x_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
v___x_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4294_, 0, v_e_4276_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
return v___x_4295_;
}
case 4:
{
lean_object* v___x_4296_; 
v___x_4296_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4296_;
}
case 5:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
lean_inc_ref(v_e_4276_);
v___x_4297_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4297_, 0, v_e_4276_);
v___x_4298_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4276_, v___x_4297_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4298_;
}
case 7:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
lean_inc_ref(v_e_4276_);
v___x_4299_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4299_, 0, v_e_4276_);
v___x_4300_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4276_, v___x_4299_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4300_;
}
case 9:
{
lean_object* v_a_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_a_4301_ = lean_ctor_get(v_e_4276_, 0);
v___x_4302_ = l_Lean_Literal_type(v_a_4301_);
v___x_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4302_);
v___x_4304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4304_, 0, v_e_4276_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
return v___x_4305_;
}
case 10:
{
lean_object* v_data_4306_; lean_object* v_expr_4307_; lean_object* v___x_4308_; 
v_data_4306_ = lean_ctor_get(v_e_4276_, 0);
v_expr_4307_ = lean_ctor_get(v_e_4276_, 1);
lean_inc_ref(v_expr_4307_);
v___x_4308_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4307_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4331_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4311_ = v___x_4308_;
v_isShared_4312_ = v_isSharedCheck_4331_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4331_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v_expr_4313_; lean_object* v_type_x3f_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4330_; 
v_expr_4313_ = lean_ctor_get(v_a_4309_, 0);
v_type_x3f_4314_ = lean_ctor_get(v_a_4309_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_a_4309_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4316_ = v_a_4309_;
v_isShared_4317_ = v_isSharedCheck_4330_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_type_x3f_4314_);
lean_inc(v_expr_4313_);
lean_dec(v_a_4309_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4330_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___y_4319_; size_t v___x_4326_; size_t v___x_4327_; uint8_t v___x_4328_; 
v___x_4326_ = lean_ptr_addr(v_expr_4307_);
v___x_4327_ = lean_ptr_addr(v_expr_4313_);
v___x_4328_ = lean_usize_dec_eq(v___x_4326_, v___x_4327_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; 
lean_inc(v_data_4306_);
lean_dec_ref_known(v_e_4276_, 2);
v___x_4329_ = l_Lean_Expr_mdata___override(v_data_4306_, v_expr_4313_);
v___y_4319_ = v___x_4329_;
goto v___jp_4318_;
}
else
{
lean_dec_ref(v_expr_4313_);
v___y_4319_ = v_e_4276_;
goto v___jp_4318_;
}
v___jp_4318_:
{
lean_object* v___x_4321_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v___y_4319_);
v___x_4321_ = v___x_4316_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___y_4319_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_type_x3f_4314_);
v___x_4321_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4323_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 0, v___x_4321_);
v___x_4323_ = v___x_4311_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4276_, 2);
return v___x_4308_;
}
}
case 11:
{
lean_object* v_typeName_4332_; lean_object* v_idx_4333_; lean_object* v_struct_4334_; lean_object* v___f_4335_; lean_object* v___x_4336_; 
v_typeName_4332_ = lean_ctor_get(v_e_4276_, 0);
v_idx_4333_ = lean_ctor_get(v_e_4276_, 1);
v_struct_4334_ = lean_ctor_get(v_e_4276_, 2);
lean_inc(v_idx_4333_);
lean_inc(v_typeName_4332_);
lean_inc_ref(v_e_4276_);
lean_inc_ref(v_struct_4334_);
v___f_4335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4335_, 0, v_struct_4334_);
lean_closure_set(v___f_4335_, 1, v_e_4276_);
lean_closure_set(v___f_4335_, 2, v_typeName_4332_);
lean_closure_set(v___f_4335_, 3, v_idx_4333_);
v___x_4336_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4276_, v___f_4335_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4336_;
}
default: 
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
lean_inc_ref(v_e_4276_);
v___x_4337_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4337_, 0, v_e_4276_);
v___x_4338_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4276_, v___x_4337_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4338_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4276_ = stack[0].m_obj;
lean_object* v___y_4277_ = stack[1].m_obj;
lean_object* v___y_4278_ = stack[2].m_obj;
lean_object* v___y_4279_ = stack[3].m_obj;
lean_object* v___y_4280_ = stack[4].m_obj;
lean_object* v___y_4281_ = stack[5].m_obj;
lean_object* v___y_4282_ = stack[6].m_obj;
lean_object* v_res_4339_;
v_res_4339_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
stack->m_obj
 = v_res_4339_;
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4340_; double v___x_4341_; 
v___x_4340_ = lean_unsigned_to_nat(1000000000u);
v___x_4341_ = lean_float_of_nat(v___x_4340_);
return v___x_4341_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_toCold_4350_; lean_object* v_options_4351_; uint8_t v_hasTrace_4352_; 
v_toCold_4350_ = lean_ctor_get(v_a_4347_, 0);
v_options_4351_ = lean_ctor_get(v_toCold_4350_, 2);
v_hasTrace_4352_ = lean_ctor_get_uint8(v_options_4351_, sizeof(void*)*1);
if (v_hasTrace_4352_ == 0)
{
lean_object* v___x_4353_; 
v___x_4353_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
return v___x_4353_;
}
else
{
lean_object* v_inheritedTraceOptions_4354_; lean_object* v___f_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v_a_4363_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v_a_4378_; 
v_inheritedTraceOptions_4354_ = lean_ctor_get(v_toCold_4350_, 11);
lean_inc_ref(v_e_4342_);
v___f_4355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4355_, 0, v_e_4342_);
v___x_4356_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4357_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4358_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4359_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4354_, v_options_4351_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4436_ = l_Lean_trace_profiler;
v___x_4437_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4351_, v___x_4436_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; 
lean_dec_ref(v___f_4355_);
v___x_4438_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
return v___x_4438_;
}
else
{
goto v___jp_4387_;
}
}
else
{
goto v___jp_4387_;
}
v___jp_4360_:
{
lean_object* v___x_4364_; double v___x_4365_; double v___x_4366_; double v___x_4367_; double v___x_4368_; double v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4364_ = lean_io_mono_nanos_now();
v___x_4365_ = lean_float_of_nat(v___y_4361_);
v___x_4366_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4367_ = lean_float_div(v___x_4365_, v___x_4366_);
v___x_4368_ = lean_float_of_nat(v___x_4364_);
v___x_4369_ = lean_float_div(v___x_4368_, v___x_4366_);
v___x_4370_ = lean_box_float(v___x_4367_);
v___x_4371_ = lean_box_float(v___x_4369_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4373_, 0, v_a_4363_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4356_, v_hasTrace_4352_, v___x_4357_, v_options_4351_, v___x_4359_, v___y_4362_, v___f_4355_, v___x_4373_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
return v___x_4374_;
}
v___jp_4375_:
{
lean_object* v___x_4379_; double v___x_4380_; double v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4379_ = lean_io_get_num_heartbeats();
v___x_4380_ = lean_float_of_nat(v___y_4376_);
v___x_4381_ = lean_float_of_nat(v___x_4379_);
v___x_4382_ = lean_box_float(v___x_4380_);
v___x_4383_ = lean_box_float(v___x_4381_);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4382_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v_a_4378_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4356_, v_hasTrace_4352_, v___x_4357_, v_options_4351_, v___x_4359_, v___y_4377_, v___f_4355_, v___x_4385_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
return v___x_4386_;
}
v___jp_4387_:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4348_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v___x_4390_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4391_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4351_, v___x_4390_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4392_ = lean_io_mono_nanos_now();
v___x_4393_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4393_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
lean_ctor_set_tag(v___x_4396_, 1);
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
v___y_4361_ = v___x_4392_;
v___y_4362_ = v_a_4389_;
v_a_4363_ = v___x_4399_;
goto v___jp_4360_;
}
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
v_a_4402_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4393_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4393_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set_tag(v___x_4404_, 0);
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
v___y_4361_ = v___x_4392_;
v___y_4362_ = v_a_4389_;
v_a_4363_ = v___x_4407_;
goto v___jp_4360_;
}
}
}
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = lean_io_get_num_heartbeats();
v___x_4411_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4411_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4411_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
lean_ctor_set_tag(v___x_4414_, 1);
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
v___y_4376_ = v___x_4410_;
v___y_4377_ = v_a_4389_;
v_a_4378_ = v___x_4417_;
goto v___jp_4375_;
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
v_a_4420_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4411_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4411_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
lean_ctor_set_tag(v___x_4422_, 0);
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
v___y_4376_ = v___x_4410_;
v___y_4377_ = v_a_4389_;
v_a_4378_ = v___x_4425_;
goto v___jp_4375_;
}
}
}
}
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec_ref(v___f_4355_);
lean_dec_ref(v_e_4342_);
v_a_4428_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4388_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4388_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4342_ = stack[0].m_obj;
lean_object* v_a_4343_ = stack[1].m_obj;
lean_object* v_a_4344_ = stack[2].m_obj;
lean_object* v_a_4345_ = stack[3].m_obj;
lean_object* v_a_4346_ = stack[4].m_obj;
lean_object* v_a_4347_ = stack[5].m_obj;
lean_object* v_a_4348_ = stack[6].m_obj;
lean_object* v_res_4439_;
v_res_4439_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
stack->m_obj
 = v_res_4439_;
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4440_, lean_object* v_e_4441_, lean_object* v_typeName_4442_, lean_object* v_idx_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4440_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v___x_4453_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4441_, v_typeName_4442_, v_idx_4443_, v_a_4452_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4453_;
}
else
{
lean_dec(v_idx_4443_);
lean_dec(v_typeName_4442_);
lean_dec_ref(v_e_4441_);
return v___x_4451_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_struct_4440_ = stack[0].m_obj;
lean_object* v_e_4441_ = stack[1].m_obj;
lean_object* v_typeName_4442_ = stack[2].m_obj;
lean_object* v_idx_4443_ = stack[3].m_obj;
lean_object* v___y_4444_ = stack[4].m_obj;
lean_object* v___y_4445_ = stack[5].m_obj;
lean_object* v___y_4446_ = stack[6].m_obj;
lean_object* v___y_4447_ = stack[7].m_obj;
lean_object* v___y_4448_ = stack[8].m_obj;
lean_object* v___y_4449_ = stack[9].m_obj;
lean_object* v_res_4454_;
v_res_4454_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4440_, v_e_4441_, v_typeName_4442_, v_idx_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
stack->m_obj
 = v_res_4454_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
lean_dec(v_a_4457_);
lean_dec(v_a_4456_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4464_, lean_object* v_fvars_4465_, lean_object* v_doms_4466_, lean_object* v_e_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4464_, v_fvars_4465_, v_doms_4466_, v_e_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_);
lean_dec(v_a_4473_);
lean_dec_ref(v_a_4472_);
lean_dec(v_a_4471_);
lean_dec_ref(v_a_4470_);
lean_dec(v_a_4469_);
lean_dec(v_a_4468_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec(v___y_4477_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4485_, lean_object* v_fvars_4486_, lean_object* v_e_4487_, lean_object* v_letFVars_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4485_, v_fvars_4486_, v_e_4487_, v_letFVars_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
lean_dec(v_a_4494_);
lean_dec_ref(v_a_4493_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
lean_dec(v_a_4490_);
lean_dec(v_a_4489_);
return v_res_4496_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4497_, lean_object* v_lctx_4498_, lean_object* v_localInsts_4499_, lean_object* v_x_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4498_, v_localInsts_4499_, v_x_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_4498_ = stack[1].m_obj;
lean_object* v_localInsts_4499_ = stack[2].m_obj;
lean_object* v_x_4500_ = stack[3].m_obj;
lean_object* v___y_4501_ = stack[4].m_obj;
lean_object* v___y_4502_ = stack[5].m_obj;
lean_object* v___y_4503_ = stack[6].m_obj;
lean_object* v___y_4504_ = stack[7].m_obj;
lean_object* v___y_4505_ = stack[8].m_obj;
lean_object* v___y_4506_ = stack[9].m_obj;
lean_object* v_res_4509_;
v_res_4509_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_box(0), v_lctx_4498_, v_localInsts_4499_, v_x_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
stack->m_obj
 = v_res_4509_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4510_, lean_object* v_lctx_4511_, lean_object* v_localInsts_4512_, lean_object* v_x_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4510_, v_lctx_4511_, v_localInsts_4512_, v_x_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec(v___y_4514_);
return v_res_4521_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4522_, lean_object* v_lctx_4523_, lean_object* v_x_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4523_, v_x_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
return v___x_4532_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_4523_ = stack[1].m_obj;
lean_object* v_x_4524_ = stack[2].m_obj;
lean_object* v___y_4525_ = stack[3].m_obj;
lean_object* v___y_4526_ = stack[4].m_obj;
lean_object* v___y_4527_ = stack[5].m_obj;
lean_object* v___y_4528_ = stack[6].m_obj;
lean_object* v___y_4529_ = stack[7].m_obj;
lean_object* v___y_4530_ = stack[8].m_obj;
lean_object* v_res_4533_;
v_res_4533_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_box(0), v_lctx_4523_, v_x_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
stack->m_obj
 = v_res_4533_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4534_, lean_object* v_lctx_4535_, lean_object* v_x_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4534_, v_lctx_4535_, v_x_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec(v___y_4537_);
return v_res_4544_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4545_ = stack[0].m_obj;
lean_object* v___y_4546_ = stack[1].m_obj;
lean_object* v___y_4547_ = stack[2].m_obj;
lean_object* v___y_4548_ = stack[3].m_obj;
lean_object* v___y_4549_ = stack[4].m_obj;
lean_object* v___y_4550_ = stack[5].m_obj;
lean_object* v_res_4553_;
v_res_4553_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
stack->m_obj
 = v_res_4553_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec(v___y_4554_);
return v_res_4561_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v___x_4569_; 
v___x_4569_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4567_);
return v___x_4569_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4562_ = stack[0].m_obj;
lean_object* v___y_4563_ = stack[1].m_obj;
lean_object* v___y_4564_ = stack[2].m_obj;
lean_object* v___y_4565_ = stack[3].m_obj;
lean_object* v___y_4566_ = stack[4].m_obj;
lean_object* v___y_4567_ = stack[5].m_obj;
lean_object* v_res_4570_;
v_res_4570_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
stack->m_obj
 = v_res_4570_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4571_);
return v_res_4578_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4579_, lean_object* v_x_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v___x_4588_; 
v___x_4588_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4580_);
return v___x_4588_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4580_ = stack[1].m_obj;
lean_object* v___y_4581_ = stack[2].m_obj;
lean_object* v___y_4582_ = stack[3].m_obj;
lean_object* v___y_4583_ = stack[4].m_obj;
lean_object* v___y_4584_ = stack[5].m_obj;
lean_object* v___y_4585_ = stack[6].m_obj;
lean_object* v___y_4586_ = stack[7].m_obj;
lean_object* v_res_4589_;
v_res_4589_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_box(0), v_x_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
stack->m_obj
 = v_res_4589_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4590_, lean_object* v_x_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4590_, v_x_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec(v___y_4592_);
return v_res_4599_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4600_, lean_object* v_data_4601_, lean_object* v_ref_4602_, lean_object* v_msg_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; 
v___x_4611_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4600_, v_data_4601_, v_ref_4602_, v_msg_4603_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
return v___x_4611_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_4600_ = stack[0].m_obj;
lean_object* v_data_4601_ = stack[1].m_obj;
lean_object* v_ref_4602_ = stack[2].m_obj;
lean_object* v_msg_4603_ = stack[3].m_obj;
lean_object* v___y_4604_ = stack[4].m_obj;
lean_object* v___y_4605_ = stack[5].m_obj;
lean_object* v___y_4606_ = stack[6].m_obj;
lean_object* v___y_4607_ = stack[7].m_obj;
lean_object* v___y_4608_ = stack[8].m_obj;
lean_object* v___y_4609_ = stack[9].m_obj;
lean_object* v_res_4612_;
v_res_4612_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4600_, v_data_4601_, v_ref_4602_, v_msg_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
stack->m_obj
 = v_res_4612_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4613_, lean_object* v_data_4614_, lean_object* v_ref_4615_, lean_object* v_msg_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4613_, v_data_4614_, v_ref_4615_, v_msg_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec(v___y_4617_);
return v_res_4624_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4625_){
_start:
{
lean_object* v___x_4627_; lean_object* v_traceState_4628_; lean_object* v_traces_4629_; lean_object* v___x_4630_; lean_object* v_traceState_4631_; lean_object* v_env_4632_; lean_object* v_nextMacroScope_4633_; lean_object* v_ngen_4634_; lean_object* v_auxDeclNGen_4635_; lean_object* v_cache_4636_; lean_object* v_recordedDeps_4637_; lean_object* v_messages_4638_; lean_object* v_infoState_4639_; lean_object* v_snapshotTasks_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4661_; 
v___x_4627_ = lean_st_ref_get(v___y_4625_);
v_traceState_4628_ = lean_ctor_get(v___x_4627_, 4);
lean_inc_ref(v_traceState_4628_);
lean_dec(v___x_4627_);
v_traces_4629_ = lean_ctor_get(v_traceState_4628_, 0);
lean_inc_ref(v_traces_4629_);
lean_dec_ref(v_traceState_4628_);
v___x_4630_ = lean_st_ref_take(v___y_4625_);
v_traceState_4631_ = lean_ctor_get(v___x_4630_, 4);
v_env_4632_ = lean_ctor_get(v___x_4630_, 0);
v_nextMacroScope_4633_ = lean_ctor_get(v___x_4630_, 1);
v_ngen_4634_ = lean_ctor_get(v___x_4630_, 2);
v_auxDeclNGen_4635_ = lean_ctor_get(v___x_4630_, 3);
v_cache_4636_ = lean_ctor_get(v___x_4630_, 5);
v_recordedDeps_4637_ = lean_ctor_get(v___x_4630_, 6);
v_messages_4638_ = lean_ctor_get(v___x_4630_, 7);
v_infoState_4639_ = lean_ctor_get(v___x_4630_, 8);
v_snapshotTasks_4640_ = lean_ctor_get(v___x_4630_, 9);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4642_ = v___x_4630_;
v_isShared_4643_ = v_isSharedCheck_4661_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_snapshotTasks_4640_);
lean_inc(v_infoState_4639_);
lean_inc(v_messages_4638_);
lean_inc(v_recordedDeps_4637_);
lean_inc(v_cache_4636_);
lean_inc(v_traceState_4631_);
lean_inc(v_auxDeclNGen_4635_);
lean_inc(v_ngen_4634_);
lean_inc(v_nextMacroScope_4633_);
lean_inc(v_env_4632_);
lean_dec(v___x_4630_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4661_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
uint64_t v_tid_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4659_; 
v_tid_4644_ = lean_ctor_get_uint64(v_traceState_4631_, sizeof(void*)*1);
v_isSharedCheck_4659_ = !lean_is_exclusive(v_traceState_4631_);
if (v_isSharedCheck_4659_ == 0)
{
lean_object* v_unused_4660_; 
v_unused_4660_ = lean_ctor_get(v_traceState_4631_, 0);
lean_dec(v_unused_4660_);
v___x_4646_ = v_traceState_4631_;
v_isShared_4647_ = v_isSharedCheck_4659_;
goto v_resetjp_4645_;
}
else
{
lean_dec(v_traceState_4631_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4659_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4652_; 
v___x_4648_ = lean_unsigned_to_nat(32u);
v___x_4649_ = lean_mk_empty_array_with_capacity(v___x_4648_);
lean_dec_ref(v___x_4649_);
v___x_4650_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 0, v___x_4650_);
v___x_4652_ = v___x_4646_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4650_);
lean_ctor_set_uint64(v_reuseFailAlloc_4658_, sizeof(void*)*1, v_tid_4644_);
v___x_4652_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4654_; 
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 4, v___x_4652_);
v___x_4654_ = v___x_4642_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_env_4632_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v_nextMacroScope_4633_);
lean_ctor_set(v_reuseFailAlloc_4657_, 2, v_ngen_4634_);
lean_ctor_set(v_reuseFailAlloc_4657_, 3, v_auxDeclNGen_4635_);
lean_ctor_set(v_reuseFailAlloc_4657_, 4, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4657_, 5, v_cache_4636_);
lean_ctor_set(v_reuseFailAlloc_4657_, 6, v_recordedDeps_4637_);
lean_ctor_set(v_reuseFailAlloc_4657_, 7, v_messages_4638_);
lean_ctor_set(v_reuseFailAlloc_4657_, 8, v_infoState_4639_);
lean_ctor_set(v_reuseFailAlloc_4657_, 9, v_snapshotTasks_4640_);
v___x_4654_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = lean_st_ref_put(v___y_4625_, v___x_4654_);
v___x_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4656_, 0, v_traces_4629_);
return v___x_4656_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4625_ = stack[0].m_obj;
lean_object* v_res_4662_;
v_res_4662_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4625_);
stack->m_obj
 = v_res_4662_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4663_);
lean_dec(v___y_4663_);
return v_res_4665_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4669_);
return v___x_4671_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4666_ = stack[0].m_obj;
lean_object* v___y_4667_ = stack[1].m_obj;
lean_object* v___y_4668_ = stack[2].m_obj;
lean_object* v___y_4669_ = stack[3].m_obj;
lean_object* v_res_4672_;
v_res_4672_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
stack->m_obj
 = v_res_4672_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
return v_res_4678_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4679_, lean_object* v_msg_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_ref_4686_; lean_object* v___x_4687_; lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4733_; 
v_ref_4686_ = lean_ctor_get(v___y_4683_, 2);
v___x_4687_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4690_ = v___x_4687_;
v_isShared_4691_ = v_isSharedCheck_4733_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4687_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4733_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4692_; lean_object* v_traceState_4693_; lean_object* v_env_4694_; lean_object* v_nextMacroScope_4695_; lean_object* v_ngen_4696_; lean_object* v_auxDeclNGen_4697_; lean_object* v_cache_4698_; lean_object* v_recordedDeps_4699_; lean_object* v_messages_4700_; lean_object* v_infoState_4701_; lean_object* v_snapshotTasks_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4732_; 
v___x_4692_ = lean_st_ref_take(v___y_4684_);
v_traceState_4693_ = lean_ctor_get(v___x_4692_, 4);
v_env_4694_ = lean_ctor_get(v___x_4692_, 0);
v_nextMacroScope_4695_ = lean_ctor_get(v___x_4692_, 1);
v_ngen_4696_ = lean_ctor_get(v___x_4692_, 2);
v_auxDeclNGen_4697_ = lean_ctor_get(v___x_4692_, 3);
v_cache_4698_ = lean_ctor_get(v___x_4692_, 5);
v_recordedDeps_4699_ = lean_ctor_get(v___x_4692_, 6);
v_messages_4700_ = lean_ctor_get(v___x_4692_, 7);
v_infoState_4701_ = lean_ctor_get(v___x_4692_, 8);
v_snapshotTasks_4702_ = lean_ctor_get(v___x_4692_, 9);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4704_ = v___x_4692_;
v_isShared_4705_ = v_isSharedCheck_4732_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_snapshotTasks_4702_);
lean_inc(v_infoState_4701_);
lean_inc(v_messages_4700_);
lean_inc(v_recordedDeps_4699_);
lean_inc(v_cache_4698_);
lean_inc(v_traceState_4693_);
lean_inc(v_auxDeclNGen_4697_);
lean_inc(v_ngen_4696_);
lean_inc(v_nextMacroScope_4695_);
lean_inc(v_env_4694_);
lean_dec(v___x_4692_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4732_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
uint64_t v_tid_4706_; lean_object* v_traces_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4731_; 
v_tid_4706_ = lean_ctor_get_uint64(v_traceState_4693_, sizeof(void*)*1);
v_traces_4707_ = lean_ctor_get(v_traceState_4693_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_traceState_4693_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4709_ = v_traceState_4693_;
v_isShared_4710_ = v_isSharedCheck_4731_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_traces_4707_);
lean_dec(v_traceState_4693_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4731_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; double v___x_4713_; uint8_t v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4722_; 
v___x_4711_ = lean_box(0);
v___x_4712_ = lean_box(0);
v___x_4713_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4714_ = 0;
v___x_4715_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4716_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4716_, 0, v_cls_4679_);
lean_ctor_set(v___x_4716_, 1, v___x_4712_);
lean_ctor_set(v___x_4716_, 2, v___x_4715_);
lean_ctor_set_float(v___x_4716_, sizeof(void*)*3, v___x_4713_);
lean_ctor_set_float(v___x_4716_, sizeof(void*)*3 + 8, v___x_4713_);
lean_ctor_set_uint8(v___x_4716_, sizeof(void*)*3 + 16, v___x_4714_);
v___x_4717_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4718_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4716_);
lean_ctor_set(v___x_4718_, 1, v_a_4688_);
lean_ctor_set(v___x_4718_, 2, v___x_4717_);
lean_inc(v_ref_4686_);
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v_ref_4686_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = l_Lean_PersistentArray_push___redArg(v_traces_4707_, v___x_4719_);
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4720_);
v___x_4722_ = v___x_4709_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4720_);
lean_ctor_set_uint64(v_reuseFailAlloc_4730_, sizeof(void*)*1, v_tid_4706_);
v___x_4722_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
lean_object* v___x_4724_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 4, v___x_4722_);
v___x_4724_ = v___x_4704_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_env_4694_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_nextMacroScope_4695_);
lean_ctor_set(v_reuseFailAlloc_4729_, 2, v_ngen_4696_);
lean_ctor_set(v_reuseFailAlloc_4729_, 3, v_auxDeclNGen_4697_);
lean_ctor_set(v_reuseFailAlloc_4729_, 4, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4729_, 5, v_cache_4698_);
lean_ctor_set(v_reuseFailAlloc_4729_, 6, v_recordedDeps_4699_);
lean_ctor_set(v_reuseFailAlloc_4729_, 7, v_messages_4700_);
lean_ctor_set(v_reuseFailAlloc_4729_, 8, v_infoState_4701_);
lean_ctor_set(v_reuseFailAlloc_4729_, 9, v_snapshotTasks_4702_);
v___x_4724_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; lean_object* v___x_4727_; 
v___x_4725_ = lean_st_ref_put(v___y_4684_, v___x_4724_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 0, v___x_4711_);
v___x_4727_ = v___x_4690_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4711_);
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
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4679_ = stack[0].m_obj;
lean_object* v_msg_4680_ = stack[1].m_obj;
lean_object* v___y_4681_ = stack[2].m_obj;
lean_object* v___y_4682_ = stack[3].m_obj;
lean_object* v___y_4683_ = stack[4].m_obj;
lean_object* v___y_4684_ = stack[5].m_obj;
lean_object* v_res_4734_;
v_res_4734_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4679_, v_msg_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
stack->m_obj
 = v_res_4734_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4735_, lean_object* v_msg_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4735_, v_msg_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
return v_res_4742_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0));
v___x_4745_ = l_Lean_stringToMessageData(v___x_4744_);
return v___x_4745_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4747_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2));
v___x_4748_ = l_Lean_stringToMessageData(v___x_4747_);
return v___x_4748_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4));
v___x_4751_ = l_Lean_stringToMessageData(v___x_4750_);
return v___x_4751_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6));
v___x_4754_ = l_Lean_stringToMessageData(v___x_4753_);
return v___x_4754_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___x_4755_, lean_object* v_e_4756_, lean_object* v___x_4757_, lean_object* v___x_4758_, lean_object* v_cls_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = lean_st_mk_ref(v___x_4755_);
v___x_4766_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4756_, v___x_4757_, v___x_4765_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4838_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4769_ = v___x_4766_;
v_isShared_4770_ = v_isSharedCheck_4838_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4838_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4771_; lean_object* v_count_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4836_; 
v___x_4771_ = lean_st_ref_get(v___x_4765_);
lean_dec(v___x_4765_);
v_count_4772_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4836_ == 0)
{
lean_object* v_unused_4837_; 
v_unused_4837_ = lean_ctor_get(v___x_4771_, 1);
lean_dec(v_unused_4837_);
v___x_4774_ = v___x_4771_;
v_isShared_4775_ = v_isSharedCheck_4836_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_count_4772_);
lean_dec(v___x_4771_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4836_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
uint8_t v___x_4798_; 
v___x_4798_ = lean_nat_dec_eq(v_count_4772_, v___x_4758_);
if (v___x_4798_ == 0)
{
lean_object* v_toCold_4799_; lean_object* v_options_4800_; uint8_t v_hasTrace_4801_; 
v_toCold_4799_ = lean_ctor_get(v___y_4762_, 0);
v_options_4800_ = lean_ctor_get(v_toCold_4799_, 2);
v_hasTrace_4801_ = lean_ctor_get_uint8(v_options_4800_, sizeof(void*)*1);
if (v_hasTrace_4801_ == 0)
{
lean_dec(v_cls_4759_);
goto v___jp_4776_;
}
else
{
lean_object* v_inheritedTraceOptions_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; 
v_inheritedTraceOptions_4802_ = lean_ctor_get(v_toCold_4799_, 11);
v___x_4803_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4759_);
v___x_4804_ = l_Lean_Name_append(v___x_4803_, v_cls_4759_);
v___x_4805_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4802_, v_options_4800_, v___x_4804_);
lean_dec(v___x_4804_);
if (v___x_4805_ == 0)
{
lean_dec(v_cls_4759_);
goto v___jp_4776_;
}
else
{
lean_object* v_expr_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v_expr_4806_ = lean_ctor_get(v_a_4767_, 0);
v___x_4807_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5);
lean_inc_ref(v_expr_4806_);
v___x_4808_ = l_Lean_indentExpr(v_expr_4806_);
v___x_4809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4807_);
lean_ctor_set(v___x_4809_, 1, v___x_4808_);
v___x_4810_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4759_, v___x_4809_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_dec_ref_known(v___x_4810_, 1);
goto v___jp_4776_;
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_del_object(v___x_4774_);
lean_dec(v_count_4772_);
lean_del_object(v___x_4769_);
lean_dec(v_a_4767_);
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4819_; lean_object* v_options_4820_; uint8_t v_hasTrace_4821_; 
v_toCold_4819_ = lean_ctor_get(v___y_4762_, 0);
v_options_4820_ = lean_ctor_get(v_toCold_4819_, 2);
v_hasTrace_4821_ = lean_ctor_get_uint8(v_options_4820_, sizeof(void*)*1);
if (v_hasTrace_4821_ == 0)
{
lean_dec(v_cls_4759_);
goto v___jp_4776_;
}
else
{
lean_object* v_inheritedTraceOptions_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; 
v_inheritedTraceOptions_4822_ = lean_ctor_get(v_toCold_4819_, 11);
v___x_4823_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4759_);
v___x_4824_ = l_Lean_Name_append(v___x_4823_, v_cls_4759_);
v___x_4825_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4822_, v_options_4820_, v___x_4824_);
lean_dec(v___x_4824_);
if (v___x_4825_ == 0)
{
lean_dec(v_cls_4759_);
goto v___jp_4776_;
}
else
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7);
v___x_4827_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4759_, v___x_4826_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_dec_ref_known(v___x_4827_, 1);
goto v___jp_4776_;
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_del_object(v___x_4774_);
lean_dec(v_count_4772_);
lean_del_object(v___x_4769_);
lean_dec(v_a_4767_);
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4827_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4827_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
}
v___jp_4776_:
{
lean_object* v_expr_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4796_; 
v_expr_4777_ = lean_ctor_get(v_a_4767_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v_a_4767_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; 
v_unused_4797_ = lean_ctor_get(v_a_4767_, 1);
lean_dec(v_unused_4797_);
v___x_4779_ = v_a_4767_;
v_isShared_4780_ = v_isSharedCheck_4796_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_expr_4777_);
lean_dec(v_a_4767_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4796_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4786_; 
v___x_4781_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1);
v___x_4782_ = l_Nat_reprFast(v_count_4772_);
v___x_4783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
v___x_4784_ = l_Lean_MessageData_ofFormat(v___x_4783_);
if (v_isShared_4780_ == 0)
{
lean_ctor_set_tag(v___x_4779_, 7);
lean_ctor_set(v___x_4779_, 1, v___x_4784_);
lean_ctor_set(v___x_4779_, 0, v___x_4781_);
v___x_4786_ = v___x_4779_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
lean_object* v___x_4787_; lean_object* v___x_4789_; 
v___x_4787_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3);
if (v_isShared_4775_ == 0)
{
lean_ctor_set_tag(v___x_4774_, 7);
lean_ctor_set(v___x_4774_, 1, v___x_4787_);
lean_ctor_set(v___x_4774_, 0, v___x_4786_);
v___x_4789_ = v___x_4774_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4786_);
lean_ctor_set(v_reuseFailAlloc_4794_, 1, v___x_4787_);
v___x_4789_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4790_, 0, v_expr_4777_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 0, v___x_4790_);
v___x_4792_ = v___x_4769_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
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
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec(v___x_4765_);
lean_dec(v_cls_4759_);
v_a_4839_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4766_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4766_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4755_ = stack[0].m_obj;
lean_object* v_e_4756_ = stack[1].m_obj;
lean_object* v___x_4757_ = stack[2].m_obj;
lean_object* v___x_4758_ = stack[3].m_obj;
lean_object* v_cls_4759_ = stack[4].m_obj;
lean_object* v___y_4760_ = stack[5].m_obj;
lean_object* v___y_4761_ = stack[6].m_obj;
lean_object* v___y_4762_ = stack[7].m_obj;
lean_object* v___y_4763_ = stack[8].m_obj;
lean_object* v_res_4847_;
v_res_4847_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___x_4755_, v_e_4756_, v___x_4757_, v___x_4758_, v_cls_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
stack->m_obj
 = v_res_4847_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___x_4848_, lean_object* v_e_4849_, lean_object* v___x_4850_, lean_object* v___x_4851_, lean_object* v_cls_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___x_4848_, v_e_4849_, v___x_4850_, v___x_4851_, v_cls_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec(v___x_4851_);
lean_dec(v___x_4850_);
return v_res_4858_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(uint8_t v___x_4859_, lean_object* v___f_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___x_4911_; uint8_t v_beta_4912_; 
v___x_4911_ = l_Lean_Meta_Context_config(v___y_4861_);
v_beta_4912_ = lean_ctor_get_uint8(v___x_4911_, 13);
if (v_beta_4912_ == 0)
{
lean_dec_ref(v___x_4911_);
goto v___jp_4866_;
}
else
{
uint8_t v_iota_4913_; 
v_iota_4913_ = lean_ctor_get_uint8(v___x_4911_, 12);
if (v_iota_4913_ == 0)
{
lean_dec_ref(v___x_4911_);
goto v___jp_4866_;
}
else
{
uint8_t v_zeta_4914_; 
v_zeta_4914_ = lean_ctor_get_uint8(v___x_4911_, 15);
if (v_zeta_4914_ == 0)
{
lean_dec_ref(v___x_4911_);
goto v___jp_4866_;
}
else
{
uint8_t v_zetaHave_4915_; 
v_zetaHave_4915_ = lean_ctor_get_uint8(v___x_4911_, 18);
if (v_zetaHave_4915_ == 0)
{
lean_dec_ref(v___x_4911_);
goto v___jp_4866_;
}
else
{
uint8_t v_zetaDelta_4916_; 
v_zetaDelta_4916_ = lean_ctor_get_uint8(v___x_4911_, 16);
if (v_zetaDelta_4916_ == 0)
{
lean_dec_ref(v___x_4911_);
goto v___jp_4866_;
}
else
{
uint8_t v_etaStruct_4917_; uint8_t v_proj_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; uint8_t v___x_4922_; 
v_etaStruct_4917_ = lean_ctor_get_uint8(v___x_4911_, 10);
v_proj_4918_ = lean_ctor_get_uint8(v___x_4911_, 14);
lean_dec_ref(v___x_4911_);
v___x_4919_ = lean_box(v_proj_4918_);
v___x_4920_ = lean_obj_tag_nat(v___x_4919_);
lean_dec(v___x_4919_);
v___x_4921_ = lean_unsigned_to_nat(2u);
v___x_4922_ = lean_nat_dec_eq(v___x_4920_, v___x_4921_);
if (v___x_4922_ == 0)
{
goto v___jp_4866_;
}
else
{
uint8_t v___x_4923_; uint8_t v___x_4924_; 
v___x_4923_ = 0;
v___x_4924_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4917_, v___x_4923_);
if (v___x_4924_ == 0)
{
goto v___jp_4866_;
}
else
{
lean_object* v___x_4925_; 
v___x_4925_ = lean_apply_5(v___f_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, lean_box(0));
return v___x_4925_;
}
}
}
}
}
}
}
v___jp_4866_:
{
lean_object* v___x_4867_; uint8_t v_foApprox_4868_; uint8_t v_ctxApprox_4869_; uint8_t v_quasiPatternApprox_4870_; uint8_t v_constApprox_4871_; uint8_t v_isDefEqStuckEx_4872_; uint8_t v_unificationHints_4873_; uint8_t v_proofIrrelevance_4874_; uint8_t v_assignSyntheticOpaque_4875_; uint8_t v_offsetCnstrs_4876_; uint8_t v_transparency_4877_; uint8_t v_univApprox_4878_; uint8_t v_zetaUnused_4879_; uint8_t v_canUnfoldPredicateConfig_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4910_; 
v___x_4867_ = l_Lean_Meta_Context_config(v___y_4861_);
v_foApprox_4868_ = lean_ctor_get_uint8(v___x_4867_, 0);
v_ctxApprox_4869_ = lean_ctor_get_uint8(v___x_4867_, 1);
v_quasiPatternApprox_4870_ = lean_ctor_get_uint8(v___x_4867_, 2);
v_constApprox_4871_ = lean_ctor_get_uint8(v___x_4867_, 3);
v_isDefEqStuckEx_4872_ = lean_ctor_get_uint8(v___x_4867_, 4);
v_unificationHints_4873_ = lean_ctor_get_uint8(v___x_4867_, 5);
v_proofIrrelevance_4874_ = lean_ctor_get_uint8(v___x_4867_, 6);
v_assignSyntheticOpaque_4875_ = lean_ctor_get_uint8(v___x_4867_, 7);
v_offsetCnstrs_4876_ = lean_ctor_get_uint8(v___x_4867_, 8);
v_transparency_4877_ = lean_ctor_get_uint8(v___x_4867_, 9);
v_univApprox_4878_ = lean_ctor_get_uint8(v___x_4867_, 11);
v_zetaUnused_4879_ = lean_ctor_get_uint8(v___x_4867_, 17);
v_canUnfoldPredicateConfig_4880_ = lean_ctor_get_uint8(v___x_4867_, 19);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4882_ = v___x_4867_;
v_isShared_4883_ = v_isSharedCheck_4910_;
goto v_resetjp_4881_;
}
else
{
lean_dec(v___x_4867_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4910_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
uint8_t v___x_4884_; uint8_t v___x_4885_; lean_object* v___x_4887_; 
v___x_4884_ = 0;
v___x_4885_ = 2;
if (v_isShared_4883_ == 0)
{
v___x_4887_ = v___x_4882_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 0, v_foApprox_4868_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 1, v_ctxApprox_4869_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 2, v_quasiPatternApprox_4870_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 3, v_constApprox_4871_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 4, v_isDefEqStuckEx_4872_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 5, v_unificationHints_4873_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 6, v_proofIrrelevance_4874_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 7, v_assignSyntheticOpaque_4875_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 8, v_offsetCnstrs_4876_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 9, v_transparency_4877_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 11, v_univApprox_4878_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 17, v_zetaUnused_4879_);
lean_ctor_set_uint8(v_reuseFailAlloc_4909_, 19, v_canUnfoldPredicateConfig_4880_);
v___x_4887_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
uint8_t v_trackZetaDelta_4888_; lean_object* v_zetaDeltaSet_4889_; lean_object* v_lctx_4890_; lean_object* v_localInstances_4891_; lean_object* v_defEqCtx_x3f_4892_; lean_object* v_synthPendingDepth_4893_; lean_object* v_customCanUnfoldPredicate_x3f_4894_; uint8_t v_univApprox_4895_; uint8_t v_inTypeClassResolution_4896_; uint8_t v_cacheInferType_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4907_; 
lean_ctor_set_uint8(v___x_4887_, 10, v___x_4884_);
lean_ctor_set_uint8(v___x_4887_, 12, v___x_4859_);
lean_ctor_set_uint8(v___x_4887_, 13, v___x_4859_);
lean_ctor_set_uint8(v___x_4887_, 14, v___x_4885_);
lean_ctor_set_uint8(v___x_4887_, 15, v___x_4859_);
lean_ctor_set_uint8(v___x_4887_, 16, v___x_4859_);
lean_ctor_set_uint8(v___x_4887_, 18, v___x_4859_);
v_trackZetaDelta_4888_ = lean_ctor_get_uint8(v___y_4861_, sizeof(void*)*7);
v_zetaDeltaSet_4889_ = lean_ctor_get(v___y_4861_, 1);
v_lctx_4890_ = lean_ctor_get(v___y_4861_, 2);
v_localInstances_4891_ = lean_ctor_get(v___y_4861_, 3);
v_defEqCtx_x3f_4892_ = lean_ctor_get(v___y_4861_, 4);
v_synthPendingDepth_4893_ = lean_ctor_get(v___y_4861_, 5);
v_customCanUnfoldPredicate_x3f_4894_ = lean_ctor_get(v___y_4861_, 6);
v_univApprox_4895_ = lean_ctor_get_uint8(v___y_4861_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4896_ = lean_ctor_get_uint8(v___y_4861_, sizeof(void*)*7 + 2);
v_cacheInferType_4897_ = lean_ctor_get_uint8(v___y_4861_, sizeof(void*)*7 + 3);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___y_4861_);
if (v_isSharedCheck_4907_ == 0)
{
lean_object* v_unused_4908_; 
v_unused_4908_ = lean_ctor_get(v___y_4861_, 0);
lean_dec(v_unused_4908_);
v___x_4899_ = v___y_4861_;
v_isShared_4900_ = v_isSharedCheck_4907_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4894_);
lean_inc(v_synthPendingDepth_4893_);
lean_inc(v_defEqCtx_x3f_4892_);
lean_inc(v_localInstances_4891_);
lean_inc(v_lctx_4890_);
lean_inc(v_zetaDeltaSet_4889_);
lean_dec(v___y_4861_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4907_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
uint64_t v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4901_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4887_);
v___x_4902_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4902_, 0, v___x_4887_);
lean_ctor_set_uint64(v___x_4902_, sizeof(void*)*1, v___x_4901_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4902_);
v___x_4904_ = v___x_4899_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4902_);
lean_ctor_set(v_reuseFailAlloc_4906_, 1, v_zetaDeltaSet_4889_);
lean_ctor_set(v_reuseFailAlloc_4906_, 2, v_lctx_4890_);
lean_ctor_set(v_reuseFailAlloc_4906_, 3, v_localInstances_4891_);
lean_ctor_set(v_reuseFailAlloc_4906_, 4, v_defEqCtx_x3f_4892_);
lean_ctor_set(v_reuseFailAlloc_4906_, 5, v_synthPendingDepth_4893_);
lean_ctor_set(v_reuseFailAlloc_4906_, 6, v_customCanUnfoldPredicate_x3f_4894_);
lean_ctor_set_uint8(v_reuseFailAlloc_4906_, sizeof(void*)*7, v_trackZetaDelta_4888_);
lean_ctor_set_uint8(v_reuseFailAlloc_4906_, sizeof(void*)*7 + 1, v_univApprox_4895_);
lean_ctor_set_uint8(v_reuseFailAlloc_4906_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4896_);
lean_ctor_set_uint8(v_reuseFailAlloc_4906_, sizeof(void*)*7 + 3, v_cacheInferType_4897_);
v___x_4904_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4905_; 
v___x_4905_ = lean_apply_5(v___f_4860_, v___x_4904_, v___y_4862_, v___y_4863_, v___y_4864_, lean_box(0));
return v___x_4905_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4859_ = stack[0].m_num;
lean_object* v___f_4860_ = stack[1].m_obj;
lean_object* v___y_4861_ = stack[2].m_obj;
lean_object* v___y_4862_ = stack[3].m_obj;
lean_object* v___y_4863_ = stack[4].m_obj;
lean_object* v___y_4864_ = stack[5].m_obj;
lean_object* v_res_4926_;
v_res_4926_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4859_, v___f_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
stack->m_obj
 = v_res_4926_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4927_, lean_object* v___f_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
uint8_t v___x_14227__boxed_4934_; lean_object* v_res_4935_; 
v___x_14227__boxed_4934_ = lean_unbox(v___x_4927_);
v_res_4935_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_14227__boxed_4934_, v___f_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
return v_res_4935_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4936_, lean_object* v_cache_4937_, lean_object* v_a_x3f_4938_){
_start:
{
lean_object* v___x_4940_; lean_object* v_mctx_4941_; lean_object* v_zetaDeltaFVarIds_4942_; lean_object* v_postponed_4943_; lean_object* v_diag_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4954_; 
v___x_4940_ = lean_st_ref_take(v___y_4936_);
v_mctx_4941_ = lean_ctor_get(v___x_4940_, 0);
v_zetaDeltaFVarIds_4942_ = lean_ctor_get(v___x_4940_, 2);
v_postponed_4943_ = lean_ctor_get(v___x_4940_, 3);
v_diag_4944_ = lean_ctor_get(v___x_4940_, 4);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4954_ == 0)
{
lean_object* v_unused_4955_; 
v_unused_4955_ = lean_ctor_get(v___x_4940_, 1);
lean_dec(v_unused_4955_);
v___x_4946_ = v___x_4940_;
v_isShared_4947_ = v_isSharedCheck_4954_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_diag_4944_);
lean_inc(v_postponed_4943_);
lean_inc(v_zetaDeltaFVarIds_4942_);
lean_inc(v_mctx_4941_);
lean_dec(v___x_4940_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4954_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4948_; lean_object* v___x_4950_; 
v___x_4948_ = lean_box(0);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 1, v_cache_4937_);
v___x_4950_ = v___x_4946_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_mctx_4941_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v_cache_4937_);
lean_ctor_set(v_reuseFailAlloc_4953_, 2, v_zetaDeltaFVarIds_4942_);
lean_ctor_set(v_reuseFailAlloc_4953_, 3, v_postponed_4943_);
lean_ctor_set(v_reuseFailAlloc_4953_, 4, v_diag_4944_);
v___x_4950_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4951_ = lean_st_ref_put(v___y_4936_, v___x_4950_);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4948_);
return v___x_4952_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4936_ = stack[0].m_obj;
lean_object* v_cache_4937_ = stack[1].m_obj;
lean_object* v_a_x3f_4938_ = stack[2].m_obj;
lean_object* v_res_4956_;
v_res_4956_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4936_, v_cache_4937_, v_a_x3f_4938_);
stack->m_obj
 = v_res_4956_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4957_, lean_object* v_cache_4958_, lean_object* v_a_x3f_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4957_, v_cache_4958_, v_a_x3f_4959_);
lean_dec(v_a_x3f_4959_);
lean_dec(v___y_4957_);
return v_res_4961_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(lean_object* v___y_4962_, lean_object* v_zetaDeltaFVarIds_4963_, lean_object* v_a_x3f_4964_){
_start:
{
lean_object* v___x_4966_; lean_object* v_mctx_4967_; lean_object* v_cache_4968_; lean_object* v_postponed_4969_; lean_object* v_diag_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4980_; 
v___x_4966_ = lean_st_ref_take(v___y_4962_);
v_mctx_4967_ = lean_ctor_get(v___x_4966_, 0);
v_cache_4968_ = lean_ctor_get(v___x_4966_, 1);
v_postponed_4969_ = lean_ctor_get(v___x_4966_, 3);
v_diag_4970_ = lean_ctor_get(v___x_4966_, 4);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4980_ == 0)
{
lean_object* v_unused_4981_; 
v_unused_4981_ = lean_ctor_get(v___x_4966_, 2);
lean_dec(v_unused_4981_);
v___x_4972_ = v___x_4966_;
v_isShared_4973_ = v_isSharedCheck_4980_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_diag_4970_);
lean_inc(v_postponed_4969_);
lean_inc(v_cache_4968_);
lean_inc(v_mctx_4967_);
lean_dec(v___x_4966_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4980_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v___x_4976_; 
v___x_4974_ = lean_box(0);
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 2, v_zetaDeltaFVarIds_4963_);
v___x_4976_ = v___x_4972_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_mctx_4967_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v_cache_4968_);
lean_ctor_set(v_reuseFailAlloc_4979_, 2, v_zetaDeltaFVarIds_4963_);
lean_ctor_set(v_reuseFailAlloc_4979_, 3, v_postponed_4969_);
lean_ctor_set(v_reuseFailAlloc_4979_, 4, v_diag_4970_);
v___x_4976_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4977_ = lean_st_ref_put(v___y_4962_, v___x_4976_);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4974_);
return v___x_4978_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4962_ = stack[0].m_obj;
lean_object* v_zetaDeltaFVarIds_4963_ = stack[1].m_obj;
lean_object* v_a_x3f_4964_ = stack[2].m_obj;
lean_object* v_res_4982_;
v_res_4982_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4962_, v_zetaDeltaFVarIds_4963_, v_a_x3f_4964_);
stack->m_obj
 = v_res_4982_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___y_4983_, lean_object* v_zetaDeltaFVarIds_4984_, lean_object* v_a_x3f_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4983_, v_zetaDeltaFVarIds_4984_, v_a_x3f_4985_);
lean_dec(v_a_x3f_4985_);
lean_dec(v___y_4983_);
return v_res_4987_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4991_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1));
v___x_4992_ = l_Lean_MessageData_ofFormat(v___x_4991_);
return v___x_4992_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3(void){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4993_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4994_ = lean_unsigned_to_nat(0u);
v___x_4995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
lean_ctor_set(v___x_4995_, 1, v___x_4993_);
return v___x_4995_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4996_);
return v___x_4997_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4999_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4998_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
lean_ctor_set(v___x_4999_, 2, v___x_4998_);
lean_ctor_set(v___x_4999_, 3, v___x_4998_);
lean_ctor_set(v___x_4999_, 4, v___x_4998_);
lean_ctor_set(v___x_4999_, 5, v___x_4998_);
return v___x_4999_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_5000_, lean_object* v_e_5001_, lean_object* v_cls_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
if (v___x_5000_ == 0)
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_dec(v_cls_5002_);
v___x_5008_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5009_, 0, v_e_5001_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
return v___x_5010_;
}
else
{
uint8_t v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___f_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v_cache_5018_; lean_object* v_a_5020_; lean_object* v___x_5031_; lean_object* v_mctx_5032_; lean_object* v_zetaDeltaFVarIds_5033_; lean_object* v_postponed_5034_; lean_object* v_diag_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5113_; 
v___x_5011_ = 0;
v___x_5012_ = lean_box(0);
v___x_5013_ = lean_unsigned_to_nat(0u);
v___x_5014_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___f_5015_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5015_, 0, v___x_5014_);
lean_closure_set(v___f_5015_, 1, v_e_5001_);
lean_closure_set(v___f_5015_, 2, v___x_5012_);
lean_closure_set(v___f_5015_, 3, v___x_5013_);
lean_closure_set(v___f_5015_, 4, v_cls_5002_);
v___x_5016_ = lean_box(1);
v___x_5017_ = lean_st_ref_get(v___y_5004_);
v_cache_5018_ = lean_ctor_get(v___x_5017_, 1);
lean_inc_ref(v_cache_5018_);
lean_dec(v___x_5017_);
v___x_5031_ = lean_st_ref_take(v___y_5004_);
v_mctx_5032_ = lean_ctor_get(v___x_5031_, 0);
v_zetaDeltaFVarIds_5033_ = lean_ctor_get(v___x_5031_, 2);
v_postponed_5034_ = lean_ctor_get(v___x_5031_, 3);
v_diag_5035_ = lean_ctor_get(v___x_5031_, 4);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5113_ == 0)
{
lean_object* v_unused_5114_; 
v_unused_5114_ = lean_ctor_get(v___x_5031_, 1);
lean_dec(v_unused_5114_);
v___x_5037_ = v___x_5031_;
v_isShared_5038_ = v_isSharedCheck_5113_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_diag_5035_);
lean_inc(v_postponed_5034_);
lean_inc(v_zetaDeltaFVarIds_5033_);
lean_inc(v_mctx_5032_);
lean_dec(v___x_5031_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5113_;
goto v_resetjp_5036_;
}
v___jp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
v___x_5021_ = lean_box(0);
v___x_5022_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_5004_, v_cache_5018_, v___x_5021_);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5029_ == 0)
{
lean_object* v_unused_5030_; 
v_unused_5030_ = lean_ctor_get(v___x_5022_, 0);
lean_dec(v_unused_5030_);
v___x_5024_ = v___x_5022_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_dec(v___x_5022_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 1);
lean_ctor_set(v___x_5024_, 0, v_a_5020_);
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5020_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
v_resetjp_5036_:
{
lean_object* v___x_5039_; lean_object* v___x_5041_; 
v___x_5039_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
if (v_isShared_5038_ == 0)
{
lean_ctor_set(v___x_5037_, 1, v___x_5039_);
v___x_5041_ = v___x_5037_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_mctx_5032_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v___x_5039_);
lean_ctor_set(v_reuseFailAlloc_5112_, 2, v_zetaDeltaFVarIds_5033_);
lean_ctor_set(v_reuseFailAlloc_5112_, 3, v_postponed_5034_);
lean_ctor_set(v_reuseFailAlloc_5112_, 4, v_diag_5035_);
v___x_5041_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
lean_object* v___x_5042_; lean_object* v_keyedConfig_5043_; lean_object* v_zetaDeltaSet_5044_; lean_object* v_lctx_5045_; lean_object* v_localInstances_5046_; lean_object* v_defEqCtx_x3f_5047_; lean_object* v_synthPendingDepth_5048_; lean_object* v_customCanUnfoldPredicate_x3f_5049_; uint8_t v_univApprox_5050_; uint8_t v_inTypeClassResolution_5051_; uint8_t v_cacheInferType_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v_mctx_5055_; lean_object* v_cache_5056_; lean_object* v_zetaDeltaFVarIds_5057_; lean_object* v_postponed_5058_; lean_object* v_diag_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5111_; 
v___x_5042_ = lean_st_ref_put(v___y_5004_, v___x_5041_);
v_keyedConfig_5043_ = lean_ctor_get(v___y_5003_, 0);
v_zetaDeltaSet_5044_ = lean_ctor_get(v___y_5003_, 1);
v_lctx_5045_ = lean_ctor_get(v___y_5003_, 2);
v_localInstances_5046_ = lean_ctor_get(v___y_5003_, 3);
v_defEqCtx_x3f_5047_ = lean_ctor_get(v___y_5003_, 4);
v_synthPendingDepth_5048_ = lean_ctor_get(v___y_5003_, 5);
v_customCanUnfoldPredicate_x3f_5049_ = lean_ctor_get(v___y_5003_, 6);
v_univApprox_5050_ = lean_ctor_get_uint8(v___y_5003_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5051_ = lean_ctor_get_uint8(v___y_5003_, sizeof(void*)*7 + 2);
v_cacheInferType_5052_ = lean_ctor_get_uint8(v___y_5003_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_5049_);
lean_inc(v_synthPendingDepth_5048_);
lean_inc(v_defEqCtx_x3f_5047_);
lean_inc_ref(v_localInstances_5046_);
lean_inc_ref(v_lctx_5045_);
lean_inc(v_zetaDeltaSet_5044_);
lean_inc_ref(v_keyedConfig_5043_);
v___x_5053_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5053_, 0, v_keyedConfig_5043_);
lean_ctor_set(v___x_5053_, 1, v_zetaDeltaSet_5044_);
lean_ctor_set(v___x_5053_, 2, v_lctx_5045_);
lean_ctor_set(v___x_5053_, 3, v_localInstances_5046_);
lean_ctor_set(v___x_5053_, 4, v_defEqCtx_x3f_5047_);
lean_ctor_set(v___x_5053_, 5, v_synthPendingDepth_5048_);
lean_ctor_set(v___x_5053_, 6, v_customCanUnfoldPredicate_x3f_5049_);
lean_ctor_set_uint8(v___x_5053_, sizeof(void*)*7, v___x_5000_);
lean_ctor_set_uint8(v___x_5053_, sizeof(void*)*7 + 1, v_univApprox_5050_);
lean_ctor_set_uint8(v___x_5053_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5051_);
lean_ctor_set_uint8(v___x_5053_, sizeof(void*)*7 + 3, v_cacheInferType_5052_);
v___x_5054_ = lean_st_ref_take(v___y_5004_);
v_mctx_5055_ = lean_ctor_get(v___x_5054_, 0);
v_cache_5056_ = lean_ctor_get(v___x_5054_, 1);
v_zetaDeltaFVarIds_5057_ = lean_ctor_get(v___x_5054_, 2);
v_postponed_5058_ = lean_ctor_get(v___x_5054_, 3);
v_diag_5059_ = lean_ctor_get(v___x_5054_, 4);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5061_ = v___x_5054_;
v_isShared_5062_ = v_isSharedCheck_5111_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_diag_5059_);
lean_inc(v_postponed_5058_);
lean_inc(v_zetaDeltaFVarIds_5057_);
lean_inc(v_cache_5056_);
lean_inc(v_mctx_5055_);
lean_dec(v___x_5054_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5111_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v_a_5064_; lean_object* v_a_5068_; lean_object* v___y_5081_; lean_object* v___y_5085_; lean_object* v___x_5089_; 
if (v_isShared_5062_ == 0)
{
lean_ctor_set(v___x_5061_, 2, v___x_5016_);
v___x_5089_ = v___x_5061_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_mctx_5055_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v_cache_5056_);
lean_ctor_set(v_reuseFailAlloc_5110_, 2, v___x_5016_);
lean_ctor_set(v_reuseFailAlloc_5110_, 3, v_postponed_5058_);
lean_ctor_set(v_reuseFailAlloc_5110_, 4, v_diag_5059_);
v___x_5089_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5088_;
}
v___jp_5063_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = lean_box(0);
v___x_5066_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_5004_, v_zetaDeltaFVarIds_5057_, v___x_5065_);
lean_dec_ref(v___x_5066_);
v_a_5020_ = v_a_5064_;
goto v___jp_5019_;
}
v___jp_5067_:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_inc(v_a_5068_);
v___x_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5069_, 0, v_a_5068_);
v___x_5070_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_5004_, v_zetaDeltaFVarIds_5057_, v___x_5069_);
lean_dec_ref(v___x_5070_);
v___x_5071_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_5004_, v_cache_5018_, v___x_5069_);
lean_dec_ref_known(v___x_5069_, 1);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5078_ == 0)
{
lean_object* v_unused_5079_; 
v_unused_5079_ = lean_ctor_get(v___x_5071_, 0);
lean_dec(v_unused_5079_);
v___x_5073_ = v___x_5071_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_dec(v___x_5071_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v_a_5068_);
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5068_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
v___jp_5080_:
{
if (lean_obj_tag(v___y_5081_) == 0)
{
lean_object* v_a_5082_; 
v_a_5082_ = lean_ctor_get(v___y_5081_, 0);
lean_inc(v_a_5082_);
lean_dec_ref_known(v___y_5081_, 1);
v_a_5068_ = v_a_5082_;
goto v___jp_5067_;
}
else
{
lean_object* v_a_5083_; 
v_a_5083_ = lean_ctor_get(v___y_5081_, 0);
lean_inc(v_a_5083_);
lean_dec_ref_known(v___y_5081_, 1);
v_a_5064_ = v_a_5083_;
goto v___jp_5063_;
}
}
v___jp_5084_:
{
if (lean_obj_tag(v___y_5085_) == 0)
{
lean_object* v_a_5086_; 
v_a_5086_ = lean_ctor_get(v___y_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___y_5085_, 1);
v_a_5068_ = v_a_5086_;
goto v___jp_5067_;
}
else
{
lean_object* v_a_5087_; 
v_a_5087_ = lean_ctor_get(v___y_5085_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___y_5085_, 1);
v_a_5064_ = v_a_5087_;
goto v___jp_5063_;
}
}
v_reusejp_5088_:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; uint8_t v_transparency_5092_; uint8_t v___x_5093_; 
v___x_5090_ = lean_st_ref_put(v___y_5004_, v___x_5089_);
v___x_5091_ = l_Lean_Meta_Context_config(v___x_5053_);
v_transparency_5092_ = lean_ctor_get_uint8(v___x_5091_, 9);
lean_dec_ref(v___x_5091_);
v___x_5093_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_5092_, v___x_5011_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v_transparency_5097_; uint8_t v___x_5098_; uint8_t v___x_5099_; 
lean_dec_ref_known(v___x_5053_, 7);
lean_inc_ref(v_keyedConfig_5043_);
v___x_5094_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_5011_, v_keyedConfig_5043_);
lean_inc(v_customCanUnfoldPredicate_x3f_5049_);
lean_inc(v_synthPendingDepth_5048_);
lean_inc(v_defEqCtx_x3f_5047_);
lean_inc_ref(v_localInstances_5046_);
lean_inc_ref(v_lctx_5045_);
lean_inc(v_zetaDeltaSet_5044_);
lean_inc_ref(v___x_5094_);
v___x_5095_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5095_, 0, v___x_5094_);
lean_ctor_set(v___x_5095_, 1, v_zetaDeltaSet_5044_);
lean_ctor_set(v___x_5095_, 2, v_lctx_5045_);
lean_ctor_set(v___x_5095_, 3, v_localInstances_5046_);
lean_ctor_set(v___x_5095_, 4, v_defEqCtx_x3f_5047_);
lean_ctor_set(v___x_5095_, 5, v_synthPendingDepth_5048_);
lean_ctor_set(v___x_5095_, 6, v_customCanUnfoldPredicate_x3f_5049_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*7, v___x_5000_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*7 + 1, v_univApprox_5050_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5051_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*7 + 3, v_cacheInferType_5052_);
v___x_5096_ = l_Lean_Meta_Context_config(v___x_5095_);
v_transparency_5097_ = lean_ctor_get_uint8(v___x_5096_, 9);
lean_dec_ref(v___x_5096_);
v___x_5098_ = 1;
v___x_5099_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_5097_, v___x_5098_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; 
lean_dec_ref(v___x_5094_);
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
v___x_5100_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_5000_, v___f_5015_, v___x_5095_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5081_ = v___x_5100_;
goto v___jp_5080_;
}
else
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
lean_dec_ref_known(v___x_5095_, 7);
v___x_5101_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_5098_, v___x_5094_);
lean_inc(v_customCanUnfoldPredicate_x3f_5049_);
lean_inc(v_synthPendingDepth_5048_);
lean_inc(v_defEqCtx_x3f_5047_);
lean_inc_ref(v_localInstances_5046_);
lean_inc_ref(v_lctx_5045_);
lean_inc(v_zetaDeltaSet_5044_);
v___x_5102_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
lean_ctor_set(v___x_5102_, 1, v_zetaDeltaSet_5044_);
lean_ctor_set(v___x_5102_, 2, v_lctx_5045_);
lean_ctor_set(v___x_5102_, 3, v_localInstances_5046_);
lean_ctor_set(v___x_5102_, 4, v_defEqCtx_x3f_5047_);
lean_ctor_set(v___x_5102_, 5, v_synthPendingDepth_5048_);
lean_ctor_set(v___x_5102_, 6, v_customCanUnfoldPredicate_x3f_5049_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*7, v___x_5000_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*7 + 1, v_univApprox_5050_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5051_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*7 + 3, v_cacheInferType_5052_);
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
v___x_5103_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_5000_, v___f_5015_, v___x_5102_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5081_ = v___x_5103_;
goto v___jp_5080_;
}
}
else
{
uint8_t v___x_5104_; uint8_t v___x_5105_; 
v___x_5104_ = 1;
v___x_5105_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_5092_, v___x_5104_);
if (v___x_5105_ == 0)
{
lean_object* v___x_5106_; 
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
v___x_5106_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_5093_, v___f_5015_, v___x_5053_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5085_ = v___x_5106_;
goto v___jp_5084_;
}
else
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
lean_dec_ref_known(v___x_5053_, 7);
lean_inc_ref(v_keyedConfig_5043_);
v___x_5107_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_5104_, v_keyedConfig_5043_);
lean_inc(v_customCanUnfoldPredicate_x3f_5049_);
lean_inc(v_synthPendingDepth_5048_);
lean_inc(v_defEqCtx_x3f_5047_);
lean_inc_ref(v_localInstances_5046_);
lean_inc_ref(v_lctx_5045_);
lean_inc(v_zetaDeltaSet_5044_);
v___x_5108_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
lean_ctor_set(v___x_5108_, 1, v_zetaDeltaSet_5044_);
lean_ctor_set(v___x_5108_, 2, v_lctx_5045_);
lean_ctor_set(v___x_5108_, 3, v_localInstances_5046_);
lean_ctor_set(v___x_5108_, 4, v_defEqCtx_x3f_5047_);
lean_ctor_set(v___x_5108_, 5, v_synthPendingDepth_5048_);
lean_ctor_set(v___x_5108_, 6, v_customCanUnfoldPredicate_x3f_5049_);
lean_ctor_set_uint8(v___x_5108_, sizeof(void*)*7, v___x_5000_);
lean_ctor_set_uint8(v___x_5108_, sizeof(void*)*7 + 1, v_univApprox_5050_);
lean_ctor_set_uint8(v___x_5108_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5051_);
lean_ctor_set_uint8(v___x_5108_, sizeof(void*)*7 + 3, v_cacheInferType_5052_);
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
v___x_5109_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_5093_, v___f_5015_, v___x_5108_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5085_ = v___x_5109_;
goto v___jp_5084_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_5000_ = stack[0].m_num;
lean_object* v_e_5001_ = stack[1].m_obj;
lean_object* v_cls_5002_ = stack[2].m_obj;
lean_object* v___y_5003_ = stack[3].m_obj;
lean_object* v___y_5004_ = stack[4].m_obj;
lean_object* v___y_5005_ = stack[5].m_obj;
lean_object* v___y_5006_ = stack[6].m_obj;
lean_object* v_res_5115_;
v_res_5115_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5000_, v_e_5001_, v_cls_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
stack->m_obj
 = v_res_5115_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_5116_, lean_object* v_e_5117_, lean_object* v_cls_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
uint8_t v___x_14485__boxed_5124_; lean_object* v_res_5125_; 
v___x_14485__boxed_5124_ = lean_unbox(v___x_5116_);
v_res_5125_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14485__boxed_5124_, v_e_5117_, v_cls_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
return v_res_5125_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
if (lean_obj_tag(v_x_5126_) == 0)
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5140_; 
v_a_5132_ = lean_ctor_get(v_x_5126_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v_x_5126_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5134_ = v_x_5126_;
v_isShared_5135_ = v_isSharedCheck_5140_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v_x_5126_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5140_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5136_; lean_object* v___x_5138_; 
v___x_5136_ = l_Lean_Exception_toMessageData(v_a_5132_);
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 0, v___x_5136_);
v___x_5138_ = v___x_5134_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5136_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
else
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5149_; 
v_a_5141_ = lean_ctor_get(v_x_5126_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v_x_5126_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5143_ = v_x_5126_;
v_isShared_5144_ = v_isSharedCheck_5149_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v_x_5126_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5149_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v_snd_5145_; lean_object* v___x_5147_; 
v_snd_5145_ = lean_ctor_get(v_a_5141_, 1);
lean_inc(v_snd_5145_);
lean_dec(v_a_5141_);
if (v_isShared_5144_ == 0)
{
lean_ctor_set_tag(v___x_5143_, 0);
lean_ctor_set(v___x_5143_, 0, v_snd_5145_);
v___x_5147_ = v___x_5143_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_snd_5145_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5126_ = stack[0].m_obj;
lean_object* v___y_5127_ = stack[1].m_obj;
lean_object* v___y_5128_ = stack[2].m_obj;
lean_object* v___y_5129_ = stack[3].m_obj;
lean_object* v___y_5130_ = stack[4].m_obj;
lean_object* v_res_5150_;
v_res_5150_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
stack->m_obj
 = v_res_5150_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
return v_res_5157_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5158_){
_start:
{
if (lean_obj_tag(v_x_5158_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5167_; 
v_a_5160_ = lean_ctor_get(v_x_5158_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v_x_5158_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5162_ = v_x_5158_;
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v_x_5158_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5165_; 
if (v_isShared_5163_ == 0)
{
lean_ctor_set_tag(v___x_5162_, 1);
v___x_5165_ = v___x_5162_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
v_a_5168_ = lean_ctor_get(v_x_5158_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v_x_5158_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v_x_5158_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v_x_5158_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
lean_ctor_set_tag(v___x_5170_, 0);
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
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
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5158_ = stack[0].m_obj;
lean_object* v_res_5176_;
v_res_5176_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5158_);
stack->m_obj
 = v_res_5176_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5177_);
return v_res_5179_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5180_){
_start:
{
if (lean_obj_tag(v_e_5180_) == 0)
{
uint8_t v___x_5181_; 
v___x_5181_ = 2;
return v___x_5181_;
}
else
{
uint8_t v___x_5182_; 
v___x_5182_ = 0;
return v___x_5182_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5180_ = stack[0].m_obj;
uint8_t v_res_5183_;
v_res_5183_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5180_);
stack->m_num = v_res_5183_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5184_){
_start:
{
uint8_t v_res_5185_; lean_object* v_r_5186_; 
v_res_5185_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5184_);
lean_dec_ref(v_e_5184_);
v_r_5186_ = lean_box(v_res_5185_);
return v_r_5186_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5187_, lean_object* v_data_5188_, lean_object* v_ref_5189_, lean_object* v_msg_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v_toCold_5196_; lean_object* v_currRecDepth_5197_; lean_object* v_ref_5198_; uint16_t v_optionFlags_5199_; uint8_t v_suppressElabErrors_5200_; uint8_t v_isRecordingDeps_5201_; lean_object* v_ref_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v_traceState_5205_; lean_object* v_traces_5206_; lean_object* v___x_5207_; size_t v_sz_5208_; size_t v___x_5209_; lean_object* v___x_5210_; lean_object* v_msg_5211_; lean_object* v___x_5212_; lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5251_; 
v_toCold_5196_ = lean_ctor_get(v___y_5193_, 0);
v_currRecDepth_5197_ = lean_ctor_get(v___y_5193_, 1);
v_ref_5198_ = lean_ctor_get(v___y_5193_, 2);
v_optionFlags_5199_ = lean_ctor_get_uint16(v___y_5193_, sizeof(void*)*3);
v_suppressElabErrors_5200_ = lean_ctor_get_uint8(v___y_5193_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5201_ = lean_ctor_get_uint8(v___y_5193_, sizeof(void*)*3 + 3);
v_ref_5202_ = l_Lean_replaceRef(v_ref_5189_, v_ref_5198_);
lean_inc(v_currRecDepth_5197_);
lean_inc_ref(v_toCold_5196_);
v___x_5203_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5203_, 0, v_toCold_5196_);
lean_ctor_set(v___x_5203_, 1, v_currRecDepth_5197_);
lean_ctor_set(v___x_5203_, 2, v_ref_5202_);
lean_ctor_set_uint16(v___x_5203_, sizeof(void*)*3, v_optionFlags_5199_);
lean_ctor_set_uint8(v___x_5203_, sizeof(void*)*3 + 2, v_suppressElabErrors_5200_);
lean_ctor_set_uint8(v___x_5203_, sizeof(void*)*3 + 3, v_isRecordingDeps_5201_);
v___x_5204_ = lean_st_ref_get(v___y_5194_);
v_traceState_5205_ = lean_ctor_get(v___x_5204_, 4);
lean_inc_ref(v_traceState_5205_);
lean_dec(v___x_5204_);
v_traces_5206_ = lean_ctor_get(v_traceState_5205_, 0);
lean_inc_ref(v_traces_5206_);
lean_dec_ref(v_traceState_5205_);
v___x_5207_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5206_);
lean_dec_ref(v_traces_5206_);
v_sz_5208_ = lean_array_size(v___x_5207_);
v___x_5209_ = ((size_t)0ULL);
v___x_5210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5208_, v___x_5209_, v___x_5207_);
v_msg_5211_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5211_, 0, v_data_5188_);
lean_ctor_set(v_msg_5211_, 1, v_msg_5190_);
lean_ctor_set(v_msg_5211_, 2, v___x_5210_);
v___x_5212_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5211_, v___y_5191_, v___y_5192_, v___x_5203_, v___y_5194_);
lean_dec_ref_known(v___x_5203_, 3);
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5215_ = v___x_5212_;
v_isShared_5216_ = v_isSharedCheck_5251_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5251_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5217_; lean_object* v_traceState_5218_; lean_object* v_env_5219_; lean_object* v_nextMacroScope_5220_; lean_object* v_ngen_5221_; lean_object* v_auxDeclNGen_5222_; lean_object* v_cache_5223_; lean_object* v_recordedDeps_5224_; lean_object* v_messages_5225_; lean_object* v_infoState_5226_; lean_object* v_snapshotTasks_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5250_; 
v___x_5217_ = lean_st_ref_take(v___y_5194_);
v_traceState_5218_ = lean_ctor_get(v___x_5217_, 4);
v_env_5219_ = lean_ctor_get(v___x_5217_, 0);
v_nextMacroScope_5220_ = lean_ctor_get(v___x_5217_, 1);
v_ngen_5221_ = lean_ctor_get(v___x_5217_, 2);
v_auxDeclNGen_5222_ = lean_ctor_get(v___x_5217_, 3);
v_cache_5223_ = lean_ctor_get(v___x_5217_, 5);
v_recordedDeps_5224_ = lean_ctor_get(v___x_5217_, 6);
v_messages_5225_ = lean_ctor_get(v___x_5217_, 7);
v_infoState_5226_ = lean_ctor_get(v___x_5217_, 8);
v_snapshotTasks_5227_ = lean_ctor_get(v___x_5217_, 9);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5229_ = v___x_5217_;
v_isShared_5230_ = v_isSharedCheck_5250_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_snapshotTasks_5227_);
lean_inc(v_infoState_5226_);
lean_inc(v_messages_5225_);
lean_inc(v_recordedDeps_5224_);
lean_inc(v_cache_5223_);
lean_inc(v_traceState_5218_);
lean_inc(v_auxDeclNGen_5222_);
lean_inc(v_ngen_5221_);
lean_inc(v_nextMacroScope_5220_);
lean_inc(v_env_5219_);
lean_dec(v___x_5217_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5250_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
uint64_t v_tid_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5248_; 
v_tid_5231_ = lean_ctor_get_uint64(v_traceState_5218_, sizeof(void*)*1);
v_isSharedCheck_5248_ = !lean_is_exclusive(v_traceState_5218_);
if (v_isSharedCheck_5248_ == 0)
{
lean_object* v_unused_5249_; 
v_unused_5249_ = lean_ctor_get(v_traceState_5218_, 0);
lean_dec(v_unused_5249_);
v___x_5233_ = v_traceState_5218_;
v_isShared_5234_ = v_isSharedCheck_5248_;
goto v_resetjp_5232_;
}
else
{
lean_dec(v_traceState_5218_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5248_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5239_; 
v___x_5235_ = lean_box(0);
v___x_5236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5236_, 0, v_ref_5189_);
lean_ctor_set(v___x_5236_, 1, v_a_5213_);
v___x_5237_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5187_, v___x_5236_);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v___x_5237_);
v___x_5239_ = v___x_5233_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5237_);
lean_ctor_set_uint64(v_reuseFailAlloc_5247_, sizeof(void*)*1, v_tid_5231_);
v___x_5239_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
lean_object* v___x_5241_; 
if (v_isShared_5230_ == 0)
{
lean_ctor_set(v___x_5229_, 4, v___x_5239_);
v___x_5241_ = v___x_5229_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_env_5219_);
lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_nextMacroScope_5220_);
lean_ctor_set(v_reuseFailAlloc_5246_, 2, v_ngen_5221_);
lean_ctor_set(v_reuseFailAlloc_5246_, 3, v_auxDeclNGen_5222_);
lean_ctor_set(v_reuseFailAlloc_5246_, 4, v___x_5239_);
lean_ctor_set(v_reuseFailAlloc_5246_, 5, v_cache_5223_);
lean_ctor_set(v_reuseFailAlloc_5246_, 6, v_recordedDeps_5224_);
lean_ctor_set(v_reuseFailAlloc_5246_, 7, v_messages_5225_);
lean_ctor_set(v_reuseFailAlloc_5246_, 8, v_infoState_5226_);
lean_ctor_set(v_reuseFailAlloc_5246_, 9, v_snapshotTasks_5227_);
v___x_5241_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
lean_object* v___x_5242_; lean_object* v___x_5244_; 
v___x_5242_ = lean_st_ref_put(v___y_5194_, v___x_5241_);
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 0, v___x_5235_);
v___x_5244_ = v___x_5215_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v___x_5235_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_5187_ = stack[0].m_obj;
lean_object* v_data_5188_ = stack[1].m_obj;
lean_object* v_ref_5189_ = stack[2].m_obj;
lean_object* v_msg_5190_ = stack[3].m_obj;
lean_object* v___y_5191_ = stack[4].m_obj;
lean_object* v___y_5192_ = stack[5].m_obj;
lean_object* v___y_5193_ = stack[6].m_obj;
lean_object* v___y_5194_ = stack[7].m_obj;
lean_object* v_res_5252_;
v_res_5252_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5187_, v_data_5188_, v_ref_5189_, v_msg_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
stack->m_obj
 = v_res_5252_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5253_, lean_object* v_data_5254_, lean_object* v_ref_5255_, lean_object* v_msg_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5253_, v_data_5254_, v_ref_5255_, v_msg_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
return v_res_5262_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5263_, uint8_t v_collapsed_5264_, lean_object* v_tag_5265_, lean_object* v_opts_5266_, uint8_t v_clsEnabled_5267_, lean_object* v_oldTraces_5268_, lean_object* v_msg_5269_, lean_object* v_resStartStop_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v_fst_5276_; lean_object* v_snd_5277_; lean_object* v___y_5279_; lean_object* v___y_5280_; lean_object* v_data_5281_; lean_object* v_fst_5292_; lean_object* v_snd_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; lean_object* v___y_5297_; lean_object* v_a_5298_; uint8_t v___y_5313_; double v___y_5345_; 
v_fst_5276_ = lean_ctor_get(v_resStartStop_5270_, 0);
lean_inc(v_fst_5276_);
v_snd_5277_ = lean_ctor_get(v_resStartStop_5270_, 1);
lean_inc(v_snd_5277_);
lean_dec_ref(v_resStartStop_5270_);
v_fst_5292_ = lean_ctor_get(v_snd_5277_, 0);
lean_inc(v_fst_5292_);
v_snd_5293_ = lean_ctor_get(v_snd_5277_, 1);
lean_inc(v_snd_5293_);
lean_dec(v_snd_5277_);
v___x_5294_ = l_Lean_trace_profiler;
v___x_5295_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5266_, v___x_5294_);
if (v___x_5295_ == 0)
{
v___y_5313_ = v___x_5295_;
goto v___jp_5312_;
}
else
{
lean_object* v___x_5350_; uint8_t v___x_5351_; 
v___x_5350_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5351_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5266_, v___x_5350_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; lean_object* v___x_5353_; double v___x_5354_; double v___x_5355_; double v___x_5356_; 
v___x_5352_ = l_Lean_trace_profiler_threshold;
v___x_5353_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5266_, v___x_5352_);
v___x_5354_ = lean_float_of_nat(v___x_5353_);
v___x_5355_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5356_ = lean_float_div(v___x_5354_, v___x_5355_);
v___y_5345_ = v___x_5356_;
goto v___jp_5344_;
}
else
{
lean_object* v___x_5357_; lean_object* v___x_5358_; double v___x_5359_; 
v___x_5357_ = l_Lean_trace_profiler_threshold;
v___x_5358_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5266_, v___x_5357_);
v___x_5359_ = lean_float_of_nat(v___x_5358_);
v___y_5345_ = v___x_5359_;
goto v___jp_5344_;
}
}
v___jp_5278_:
{
lean_object* v___x_5282_; 
lean_inc(v___y_5280_);
v___x_5282_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5268_, v_data_5281_, v___y_5280_, v___y_5279_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v___x_5283_; 
lean_dec_ref_known(v___x_5282_, 1);
v___x_5283_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5276_);
return v___x_5283_;
}
else
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
lean_dec(v_fst_5276_);
v_a_5284_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5282_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5282_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
v___jp_5296_:
{
uint8_t v_result_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; double v___x_5302_; lean_object* v_data_5303_; 
v_result_5299_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5276_);
v___x_5300_ = lean_box(v_result_5299_);
v___x_5301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5301_, 0, v___x_5300_);
v___x_5302_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5265_);
lean_inc_ref(v___x_5301_);
lean_inc(v_cls_5263_);
v_data_5303_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5303_, 0, v_cls_5263_);
lean_ctor_set(v_data_5303_, 1, v___x_5301_);
lean_ctor_set(v_data_5303_, 2, v_tag_5265_);
lean_ctor_set_float(v_data_5303_, sizeof(void*)*3, v___x_5302_);
lean_ctor_set_float(v_data_5303_, sizeof(void*)*3 + 8, v___x_5302_);
lean_ctor_set_uint8(v_data_5303_, sizeof(void*)*3 + 16, v_collapsed_5264_);
if (v___x_5295_ == 0)
{
lean_dec_ref_known(v___x_5301_, 1);
lean_dec(v_snd_5293_);
lean_dec(v_fst_5292_);
lean_dec_ref(v_tag_5265_);
lean_dec(v_cls_5263_);
v___y_5279_ = v_a_5298_;
v___y_5280_ = v___y_5297_;
v_data_5281_ = v_data_5303_;
goto v___jp_5278_;
}
else
{
lean_object* v_data_5304_; double v___x_5305_; double v___x_5306_; 
lean_dec_ref_known(v_data_5303_, 3);
v_data_5304_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5304_, 0, v_cls_5263_);
lean_ctor_set(v_data_5304_, 1, v___x_5301_);
lean_ctor_set(v_data_5304_, 2, v_tag_5265_);
v___x_5305_ = lean_unbox_float(v_fst_5292_);
lean_dec(v_fst_5292_);
lean_ctor_set_float(v_data_5304_, sizeof(void*)*3, v___x_5305_);
v___x_5306_ = lean_unbox_float(v_snd_5293_);
lean_dec(v_snd_5293_);
lean_ctor_set_float(v_data_5304_, sizeof(void*)*3 + 8, v___x_5306_);
lean_ctor_set_uint8(v_data_5304_, sizeof(void*)*3 + 16, v_collapsed_5264_);
v___y_5279_ = v_a_5298_;
v___y_5280_ = v___y_5297_;
v_data_5281_ = v_data_5304_;
goto v___jp_5278_;
}
}
v___jp_5307_:
{
lean_object* v_ref_5308_; lean_object* v___x_5309_; 
v_ref_5308_ = lean_ctor_get(v___y_5273_, 2);
lean_inc(v___y_5274_);
lean_inc_ref(v___y_5273_);
lean_inc(v___y_5272_);
lean_inc_ref(v___y_5271_);
lean_inc(v_fst_5276_);
v___x_5309_ = lean_apply_6(v_msg_5269_, v_fst_5276_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, lean_box(0));
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc(v_a_5310_);
lean_dec_ref_known(v___x_5309_, 1);
v___y_5297_ = v_ref_5308_;
v_a_5298_ = v_a_5310_;
goto v___jp_5296_;
}
else
{
lean_object* v___x_5311_; 
lean_dec_ref_known(v___x_5309_, 1);
v___x_5311_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5297_ = v_ref_5308_;
v_a_5298_ = v___x_5311_;
goto v___jp_5296_;
}
}
v___jp_5312_:
{
if (v_clsEnabled_5267_ == 0)
{
if (v___y_5313_ == 0)
{
lean_object* v___x_5314_; lean_object* v_traceState_5315_; lean_object* v_env_5316_; lean_object* v_nextMacroScope_5317_; lean_object* v_ngen_5318_; lean_object* v_auxDeclNGen_5319_; lean_object* v_cache_5320_; lean_object* v_recordedDeps_5321_; lean_object* v_messages_5322_; lean_object* v_infoState_5323_; lean_object* v_snapshotTasks_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5343_; 
lean_dec(v_snd_5293_);
lean_dec(v_fst_5292_);
lean_dec_ref(v_msg_5269_);
lean_dec_ref(v_tag_5265_);
lean_dec(v_cls_5263_);
v___x_5314_ = lean_st_ref_take(v___y_5274_);
v_traceState_5315_ = lean_ctor_get(v___x_5314_, 4);
v_env_5316_ = lean_ctor_get(v___x_5314_, 0);
v_nextMacroScope_5317_ = lean_ctor_get(v___x_5314_, 1);
v_ngen_5318_ = lean_ctor_get(v___x_5314_, 2);
v_auxDeclNGen_5319_ = lean_ctor_get(v___x_5314_, 3);
v_cache_5320_ = lean_ctor_get(v___x_5314_, 5);
v_recordedDeps_5321_ = lean_ctor_get(v___x_5314_, 6);
v_messages_5322_ = lean_ctor_get(v___x_5314_, 7);
v_infoState_5323_ = lean_ctor_get(v___x_5314_, 8);
v_snapshotTasks_5324_ = lean_ctor_get(v___x_5314_, 9);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5314_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5326_ = v___x_5314_;
v_isShared_5327_ = v_isSharedCheck_5343_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_snapshotTasks_5324_);
lean_inc(v_infoState_5323_);
lean_inc(v_messages_5322_);
lean_inc(v_recordedDeps_5321_);
lean_inc(v_cache_5320_);
lean_inc(v_traceState_5315_);
lean_inc(v_auxDeclNGen_5319_);
lean_inc(v_ngen_5318_);
lean_inc(v_nextMacroScope_5317_);
lean_inc(v_env_5316_);
lean_dec(v___x_5314_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5343_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
uint64_t v_tid_5328_; lean_object* v_traces_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5342_; 
v_tid_5328_ = lean_ctor_get_uint64(v_traceState_5315_, sizeof(void*)*1);
v_traces_5329_ = lean_ctor_get(v_traceState_5315_, 0);
v_isSharedCheck_5342_ = !lean_is_exclusive(v_traceState_5315_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5331_ = v_traceState_5315_;
v_isShared_5332_ = v_isSharedCheck_5342_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_traces_5329_);
lean_dec(v_traceState_5315_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5342_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5333_; lean_object* v___x_5335_; 
v___x_5333_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5268_, v_traces_5329_);
lean_dec_ref(v_traces_5329_);
if (v_isShared_5332_ == 0)
{
lean_ctor_set(v___x_5331_, 0, v___x_5333_);
v___x_5335_ = v___x_5331_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5333_);
lean_ctor_set_uint64(v_reuseFailAlloc_5341_, sizeof(void*)*1, v_tid_5328_);
v___x_5335_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
lean_object* v___x_5337_; 
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 4, v___x_5335_);
v___x_5337_ = v___x_5326_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_env_5316_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v_nextMacroScope_5317_);
lean_ctor_set(v_reuseFailAlloc_5340_, 2, v_ngen_5318_);
lean_ctor_set(v_reuseFailAlloc_5340_, 3, v_auxDeclNGen_5319_);
lean_ctor_set(v_reuseFailAlloc_5340_, 4, v___x_5335_);
lean_ctor_set(v_reuseFailAlloc_5340_, 5, v_cache_5320_);
lean_ctor_set(v_reuseFailAlloc_5340_, 6, v_recordedDeps_5321_);
lean_ctor_set(v_reuseFailAlloc_5340_, 7, v_messages_5322_);
lean_ctor_set(v_reuseFailAlloc_5340_, 8, v_infoState_5323_);
lean_ctor_set(v_reuseFailAlloc_5340_, 9, v_snapshotTasks_5324_);
v___x_5337_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5338_ = lean_st_ref_put(v___y_5274_, v___x_5337_);
v___x_5339_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5276_);
return v___x_5339_;
}
}
}
}
}
else
{
goto v___jp_5307_;
}
}
else
{
goto v___jp_5307_;
}
}
v___jp_5344_:
{
double v___x_5346_; double v___x_5347_; double v___x_5348_; uint8_t v___x_5349_; 
v___x_5346_ = lean_unbox_float(v_snd_5293_);
v___x_5347_ = lean_unbox_float(v_fst_5292_);
v___x_5348_ = lean_float_sub(v___x_5346_, v___x_5347_);
v___x_5349_ = lean_float_decLt(v___y_5345_, v___x_5348_);
v___y_5313_ = v___x_5349_;
goto v___jp_5312_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5263_ = stack[0].m_obj;
uint8_t v_collapsed_5264_ = stack[1].m_num;
lean_object* v_tag_5265_ = stack[2].m_obj;
lean_object* v_opts_5266_ = stack[3].m_obj;
uint8_t v_clsEnabled_5267_ = stack[4].m_num;
lean_object* v_oldTraces_5268_ = stack[5].m_obj;
lean_object* v_msg_5269_ = stack[6].m_obj;
lean_object* v_resStartStop_5270_ = stack[7].m_obj;
lean_object* v___y_5271_ = stack[8].m_obj;
lean_object* v___y_5272_ = stack[9].m_obj;
lean_object* v___y_5273_ = stack[10].m_obj;
lean_object* v___y_5274_ = stack[11].m_obj;
lean_object* v_res_5360_;
v_res_5360_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5263_, v_collapsed_5264_, v_tag_5265_, v_opts_5266_, v_clsEnabled_5267_, v_oldTraces_5268_, v_msg_5269_, v_resStartStop_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_);
stack->m_obj
 = v_res_5360_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5361_, lean_object* v_collapsed_5362_, lean_object* v_tag_5363_, lean_object* v_opts_5364_, lean_object* v_clsEnabled_5365_, lean_object* v_oldTraces_5366_, lean_object* v_msg_5367_, lean_object* v_resStartStop_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
uint8_t v_collapsed_boxed_5374_; uint8_t v_clsEnabled_boxed_5375_; lean_object* v_res_5376_; 
v_collapsed_boxed_5374_ = lean_unbox(v_collapsed_5362_);
v_clsEnabled_boxed_5375_ = lean_unbox(v_clsEnabled_5365_);
v_res_5376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5361_, v_collapsed_boxed_5374_, v_tag_5363_, v_opts_5364_, v_clsEnabled_boxed_5375_, v_oldTraces_5366_, v_msg_5367_, v_resStartStop_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec_ref(v_opts_5364_);
return v_res_5376_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v_cls_5381_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5382_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5383_ = l_Lean_Name_append(v___x_5382_, v_cls_5381_);
return v___x_5383_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_){
_start:
{
lean_object* v___y_5391_; lean_object* v_toCold_5409_; lean_object* v_options_5410_; lean_object* v_inheritedTraceOptions_5411_; uint8_t v_hasTrace_5412_; lean_object* v_cls_5413_; uint8_t v___x_5414_; 
v_toCold_5409_ = lean_ctor_get(v_a_5387_, 0);
v_options_5410_ = lean_ctor_get(v_toCold_5409_, 2);
v_inheritedTraceOptions_5411_ = lean_ctor_get(v_toCold_5409_, 11);
v_hasTrace_5412_ = lean_ctor_get_uint8(v_options_5410_, sizeof(void*)*1);
v_cls_5413_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5414_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5384_);
if (v_hasTrace_5412_ == 0)
{
lean_object* v___x_5415_; 
v___x_5415_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5414_, v_e_5384_, v_cls_5413_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
v___y_5391_ = v___x_5415_;
goto v___jp_5390_;
}
else
{
lean_object* v___f_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; lean_object* v___y_5421_; lean_object* v___y_5422_; lean_object* v_a_5423_; lean_object* v___y_5436_; lean_object* v___y_5437_; lean_object* v_a_5438_; 
v___f_5416_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5417_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5418_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5411_, v_options_5410_, v___x_5418_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5488_; uint8_t v___x_5489_; 
v___x_5488_ = l_Lean_trace_profiler;
v___x_5489_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5410_, v___x_5488_);
if (v___x_5489_ == 0)
{
lean_object* v___x_5490_; 
v___x_5490_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5414_, v_e_5384_, v_cls_5413_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
v___y_5391_ = v___x_5490_;
goto v___jp_5390_;
}
else
{
goto v___jp_5447_;
}
}
else
{
goto v___jp_5447_;
}
v___jp_5420_:
{
lean_object* v___x_5424_; double v___x_5425_; double v___x_5426_; double v___x_5427_; double v___x_5428_; double v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5424_ = lean_io_mono_nanos_now();
v___x_5425_ = lean_float_of_nat(v___y_5422_);
v___x_5426_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5427_ = lean_float_div(v___x_5425_, v___x_5426_);
v___x_5428_ = lean_float_of_nat(v___x_5424_);
v___x_5429_ = lean_float_div(v___x_5428_, v___x_5426_);
v___x_5430_ = lean_box_float(v___x_5427_);
v___x_5431_ = lean_box_float(v___x_5429_);
v___x_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5430_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5433_, 0, v_a_5423_);
lean_ctor_set(v___x_5433_, 1, v___x_5432_);
v___x_5434_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5413_, v_hasTrace_5412_, v___x_5417_, v_options_5410_, v___x_5419_, v___y_5421_, v___f_5416_, v___x_5433_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
v___y_5391_ = v___x_5434_;
goto v___jp_5390_;
}
v___jp_5435_:
{
lean_object* v___x_5439_; double v___x_5440_; double v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v___x_5439_ = lean_io_get_num_heartbeats();
v___x_5440_ = lean_float_of_nat(v___y_5437_);
v___x_5441_ = lean_float_of_nat(v___x_5439_);
v___x_5442_ = lean_box_float(v___x_5440_);
v___x_5443_ = lean_box_float(v___x_5441_);
v___x_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5442_);
lean_ctor_set(v___x_5444_, 1, v___x_5443_);
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v_a_5438_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5413_, v_hasTrace_5412_, v___x_5417_, v_options_5410_, v___x_5419_, v___y_5436_, v___f_5416_, v___x_5445_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
v___y_5391_ = v___x_5446_;
goto v___jp_5390_;
}
v___jp_5447_:
{
lean_object* v___x_5448_; lean_object* v_a_5449_; lean_object* v___x_5450_; uint8_t v___x_5451_; 
v___x_5448_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5388_);
v_a_5449_ = lean_ctor_get(v___x_5448_, 0);
lean_inc(v_a_5449_);
lean_dec_ref(v___x_5448_);
v___x_5450_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5451_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5410_, v___x_5450_);
if (v___x_5451_ == 0)
{
lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5452_ = lean_io_mono_nanos_now();
v___x_5453_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5414_, v_e_5384_, v_cls_5413_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5461_; 
v_a_5454_ = lean_ctor_get(v___x_5453_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5456_ = v___x_5453_;
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5453_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5457_ == 0)
{
lean_ctor_set_tag(v___x_5456_, 1);
v___x_5459_ = v___x_5456_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
v___y_5421_ = v_a_5449_;
v___y_5422_ = v___x_5452_;
v_a_5423_ = v___x_5459_;
goto v___jp_5420_;
}
}
}
else
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5469_; 
v_a_5462_ = lean_ctor_get(v___x_5453_, 0);
v_isSharedCheck_5469_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5469_ == 0)
{
v___x_5464_ = v___x_5453_;
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5453_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5467_; 
if (v_isShared_5465_ == 0)
{
lean_ctor_set_tag(v___x_5464_, 0);
v___x_5467_ = v___x_5464_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
v___y_5421_ = v_a_5449_;
v___y_5422_ = v___x_5452_;
v_a_5423_ = v___x_5467_;
goto v___jp_5420_;
}
}
}
}
else
{
lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5470_ = lean_io_get_num_heartbeats();
v___x_5471_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5414_, v_e_5384_, v_cls_5413_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
if (lean_obj_tag(v___x_5471_) == 0)
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5479_; 
v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5474_ = v___x_5471_;
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___x_5471_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5477_; 
if (v_isShared_5475_ == 0)
{
lean_ctor_set_tag(v___x_5474_, 1);
v___x_5477_ = v___x_5474_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
v___y_5436_ = v_a_5449_;
v___y_5437_ = v___x_5470_;
v_a_5438_ = v___x_5477_;
goto v___jp_5435_;
}
}
}
else
{
lean_object* v_a_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5487_; 
v_a_5480_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5487_ == 0)
{
v___x_5482_ = v___x_5471_;
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_a_5480_);
lean_dec(v___x_5471_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5485_; 
if (v_isShared_5483_ == 0)
{
lean_ctor_set_tag(v___x_5482_, 0);
v___x_5485_ = v___x_5482_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_a_5480_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
v___y_5436_ = v_a_5449_;
v___y_5437_ = v___x_5470_;
v_a_5438_ = v___x_5485_;
goto v___jp_5435_;
}
}
}
}
}
}
v___jp_5390_:
{
if (lean_obj_tag(v___y_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5400_; 
v_a_5392_ = lean_ctor_get(v___y_5391_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___y_5391_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5394_ = v___y_5391_;
v_isShared_5395_ = v_isSharedCheck_5400_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_a_5392_);
lean_dec(v___y_5391_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5400_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v_fst_5396_; lean_object* v___x_5398_; 
v_fst_5396_ = lean_ctor_get(v_a_5392_, 0);
lean_inc(v_fst_5396_);
lean_dec(v_a_5392_);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 0, v_fst_5396_);
v___x_5398_ = v___x_5394_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_fst_5396_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
else
{
lean_object* v_a_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5408_; 
v_a_5401_ = lean_ctor_get(v___y_5391_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___y_5391_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5403_ = v___y_5391_;
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_a_5401_);
lean_dec(v___y_5391_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v___x_5406_; 
if (v_isShared_5404_ == 0)
{
v___x_5406_ = v___x_5403_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
v___x_5406_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
return v___x_5406_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5384_ = stack[0].m_obj;
lean_object* v_a_5385_ = stack[1].m_obj;
lean_object* v_a_5386_ = stack[2].m_obj;
lean_object* v_a_5387_ = stack[3].m_obj;
lean_object* v_a_5388_ = stack[4].m_obj;
lean_object* v_res_5491_;
v_res_5491_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
stack->m_obj
 = v_res_5491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_){
_start:
{
lean_object* v_res_5498_; 
v_res_5498_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec_ref(v_a_5493_);
return v_res_5498_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5499_, lean_object* v_x_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_){
_start:
{
lean_object* v___x_5506_; 
v___x_5506_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5500_);
return v___x_5506_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5500_ = stack[1].m_obj;
lean_object* v___y_5501_ = stack[2].m_obj;
lean_object* v___y_5502_ = stack[3].m_obj;
lean_object* v___y_5503_ = stack[4].m_obj;
lean_object* v___y_5504_ = stack[5].m_obj;
lean_object* v_res_5507_;
v_res_5507_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_box(0), v_x_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_);
stack->m_obj
 = v_res_5507_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5508_, lean_object* v_x_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_){
_start:
{
lean_object* v_res_5515_; 
v_res_5515_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5508_, v_x_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_);
lean_dec(v___y_5513_);
lean_dec_ref(v___y_5512_);
lean_dec(v___y_5511_);
lean_dec_ref(v___y_5510_);
return v_res_5515_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5516_, lean_object* v___y_5517_){
_start:
{
uint8_t v___x_5519_; 
v___x_5519_ = l_Lean_Expr_hasMVar(v_e_5516_);
if (v___x_5519_ == 0)
{
lean_object* v___x_5520_; 
v___x_5520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5520_, 0, v_e_5516_);
return v___x_5520_;
}
else
{
lean_object* v___x_5521_; lean_object* v_mctx_5522_; lean_object* v___x_5523_; lean_object* v_fst_5524_; lean_object* v_snd_5525_; lean_object* v___x_5526_; lean_object* v_cache_5527_; lean_object* v_zetaDeltaFVarIds_5528_; lean_object* v_postponed_5529_; lean_object* v_diag_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5539_; 
v___x_5521_ = lean_st_ref_get(v___y_5517_);
v_mctx_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc_ref(v_mctx_5522_);
lean_dec(v___x_5521_);
v___x_5523_ = l_Lean_instantiateMVarsCore(v_mctx_5522_, v_e_5516_);
v_fst_5524_ = lean_ctor_get(v___x_5523_, 0);
lean_inc(v_fst_5524_);
v_snd_5525_ = lean_ctor_get(v___x_5523_, 1);
lean_inc(v_snd_5525_);
lean_dec_ref(v___x_5523_);
v___x_5526_ = lean_st_ref_take(v___y_5517_);
v_cache_5527_ = lean_ctor_get(v___x_5526_, 1);
v_zetaDeltaFVarIds_5528_ = lean_ctor_get(v___x_5526_, 2);
v_postponed_5529_ = lean_ctor_get(v___x_5526_, 3);
v_diag_5530_ = lean_ctor_get(v___x_5526_, 4);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5526_);
if (v_isSharedCheck_5539_ == 0)
{
lean_object* v_unused_5540_; 
v_unused_5540_ = lean_ctor_get(v___x_5526_, 0);
lean_dec(v_unused_5540_);
v___x_5532_ = v___x_5526_;
v_isShared_5533_ = v_isSharedCheck_5539_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_diag_5530_);
lean_inc(v_postponed_5529_);
lean_inc(v_zetaDeltaFVarIds_5528_);
lean_inc(v_cache_5527_);
lean_dec(v___x_5526_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5539_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5535_; 
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v_snd_5525_);
v___x_5535_ = v___x_5532_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_snd_5525_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v_cache_5527_);
lean_ctor_set(v_reuseFailAlloc_5538_, 2, v_zetaDeltaFVarIds_5528_);
lean_ctor_set(v_reuseFailAlloc_5538_, 3, v_postponed_5529_);
lean_ctor_set(v_reuseFailAlloc_5538_, 4, v_diag_5530_);
v___x_5535_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_st_ref_put(v___y_5517_, v___x_5535_);
v___x_5537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5537_, 0, v_fst_5524_);
return v___x_5537_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5516_ = stack[0].m_obj;
lean_object* v___y_5517_ = stack[1].m_obj;
lean_object* v_res_5541_;
v_res_5541_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5516_, v___y_5517_);
stack->m_obj
 = v_res_5541_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_){
_start:
{
lean_object* v_res_5545_; 
v_res_5545_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5542_, v___y_5543_);
lean_dec(v___y_5543_);
return v_res_5545_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_){
_start:
{
lean_object* v___x_5552_; 
v___x_5552_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5546_, v___y_5548_);
return v___x_5552_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5546_ = stack[0].m_obj;
lean_object* v___y_5547_ = stack[1].m_obj;
lean_object* v___y_5548_ = stack[2].m_obj;
lean_object* v___y_5549_ = stack[3].m_obj;
lean_object* v___y_5550_ = stack[4].m_obj;
lean_object* v_res_5553_;
v_res_5553_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
stack->m_obj
 = v_res_5553_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_){
_start:
{
lean_object* v_res_5560_; 
v_res_5560_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
lean_dec(v___y_5558_);
lean_dec_ref(v___y_5557_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
return v_res_5560_;
}
}
lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5561_, lean_object* v_opts_5562_, lean_object* v_act_5563_, lean_object* v_decl_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_){
_start:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; 
lean_inc(v___y_5568_);
lean_inc_ref(v___y_5567_);
lean_inc(v___y_5566_);
lean_inc_ref(v___y_5565_);
v___x_5570_ = lean_apply_4(v_act_5563_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_);
v___x_5571_ = l_Lean_profileitIOUnsafe___redArg(v_category_5561_, v_opts_5562_, v___x_5570_, v_decl_5564_);
return v___x_5571_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_5561_ = stack[0].m_obj;
lean_object* v_opts_5562_ = stack[1].m_obj;
lean_object* v_act_5563_ = stack[2].m_obj;
lean_object* v_decl_5564_ = stack[3].m_obj;
lean_object* v___y_5565_ = stack[4].m_obj;
lean_object* v___y_5566_ = stack[5].m_obj;
lean_object* v___y_5567_ = stack[6].m_obj;
lean_object* v___y_5568_ = stack[7].m_obj;
lean_object* v_res_5572_;
v_res_5572_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5561_, v_opts_5562_, v_act_5563_, v_decl_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_);
stack->m_obj
 = v_res_5572_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5573_, lean_object* v_opts_5574_, lean_object* v_act_5575_, lean_object* v_decl_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5573_, v_opts_5574_, v_act_5575_, v_decl_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
lean_dec(v___y_5580_);
lean_dec_ref(v___y_5579_);
lean_dec(v___y_5578_);
lean_dec_ref(v___y_5577_);
lean_dec_ref(v_opts_5574_);
lean_dec_ref(v_category_5573_);
return v_res_5582_;
}
}
lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5583_, lean_object* v_category_5584_, lean_object* v_opts_5585_, lean_object* v_act_5586_, lean_object* v_decl_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_){
_start:
{
lean_object* v___x_5593_; 
v___x_5593_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5584_, v_opts_5585_, v_act_5586_, v_decl_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_);
return v___x_5593_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_5584_ = stack[1].m_obj;
lean_object* v_opts_5585_ = stack[2].m_obj;
lean_object* v_act_5586_ = stack[3].m_obj;
lean_object* v_decl_5587_ = stack[4].m_obj;
lean_object* v___y_5588_ = stack[5].m_obj;
lean_object* v___y_5589_ = stack[6].m_obj;
lean_object* v___y_5590_ = stack[7].m_obj;
lean_object* v___y_5591_ = stack[8].m_obj;
lean_object* v_res_5594_;
v_res_5594_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_box(0), v_category_5584_, v_opts_5585_, v_act_5586_, v_decl_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_);
stack->m_obj
 = v_res_5594_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5595_, lean_object* v_category_5596_, lean_object* v_opts_5597_, lean_object* v_act_5598_, lean_object* v_decl_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
lean_object* v_res_5605_; 
v_res_5605_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5595_, v_category_5596_, v_opts_5597_, v_act_5598_, v_decl_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
lean_dec(v___y_5603_);
lean_dec_ref(v___y_5602_);
lean_dec(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec_ref(v_opts_5597_);
lean_dec_ref(v_category_5596_);
return v_res_5605_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5606_, uint8_t v_isExporting_5607_, lean_object* v___x_5608_, lean_object* v___y_5609_, lean_object* v___x_5610_, lean_object* v_a_x3f_5611_){
_start:
{
lean_object* v___x_5613_; lean_object* v_env_5614_; lean_object* v_nextMacroScope_5615_; lean_object* v_ngen_5616_; lean_object* v_auxDeclNGen_5617_; lean_object* v_traceState_5618_; lean_object* v_recordedDeps_5619_; lean_object* v_messages_5620_; lean_object* v_infoState_5621_; lean_object* v_snapshotTasks_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5647_; 
v___x_5613_ = lean_st_ref_take(v___y_5606_);
v_env_5614_ = lean_ctor_get(v___x_5613_, 0);
v_nextMacroScope_5615_ = lean_ctor_get(v___x_5613_, 1);
v_ngen_5616_ = lean_ctor_get(v___x_5613_, 2);
v_auxDeclNGen_5617_ = lean_ctor_get(v___x_5613_, 3);
v_traceState_5618_ = lean_ctor_get(v___x_5613_, 4);
v_recordedDeps_5619_ = lean_ctor_get(v___x_5613_, 6);
v_messages_5620_ = lean_ctor_get(v___x_5613_, 7);
v_infoState_5621_ = lean_ctor_get(v___x_5613_, 8);
v_snapshotTasks_5622_ = lean_ctor_get(v___x_5613_, 9);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; 
v_unused_5648_ = lean_ctor_get(v___x_5613_, 5);
lean_dec(v_unused_5648_);
v___x_5624_ = v___x_5613_;
v_isShared_5625_ = v_isSharedCheck_5647_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_snapshotTasks_5622_);
lean_inc(v_infoState_5621_);
lean_inc(v_messages_5620_);
lean_inc(v_recordedDeps_5619_);
lean_inc(v_traceState_5618_);
lean_inc(v_auxDeclNGen_5617_);
lean_inc(v_ngen_5616_);
lean_inc(v_nextMacroScope_5615_);
lean_inc(v_env_5614_);
lean_dec(v___x_5613_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5647_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5626_; lean_object* v___x_5628_; 
v___x_5626_ = l_Lean_Environment_setExporting(v_env_5614_, v_isExporting_5607_);
if (v_isShared_5625_ == 0)
{
lean_ctor_set(v___x_5624_, 5, v___x_5608_);
lean_ctor_set(v___x_5624_, 0, v___x_5626_);
v___x_5628_ = v___x_5624_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5626_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_nextMacroScope_5615_);
lean_ctor_set(v_reuseFailAlloc_5646_, 2, v_ngen_5616_);
lean_ctor_set(v_reuseFailAlloc_5646_, 3, v_auxDeclNGen_5617_);
lean_ctor_set(v_reuseFailAlloc_5646_, 4, v_traceState_5618_);
lean_ctor_set(v_reuseFailAlloc_5646_, 5, v___x_5608_);
lean_ctor_set(v_reuseFailAlloc_5646_, 6, v_recordedDeps_5619_);
lean_ctor_set(v_reuseFailAlloc_5646_, 7, v_messages_5620_);
lean_ctor_set(v_reuseFailAlloc_5646_, 8, v_infoState_5621_);
lean_ctor_set(v_reuseFailAlloc_5646_, 9, v_snapshotTasks_5622_);
v___x_5628_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v_mctx_5631_; lean_object* v_zetaDeltaFVarIds_5632_; lean_object* v_postponed_5633_; lean_object* v_diag_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5644_; 
v___x_5629_ = lean_st_ref_put(v___y_5606_, v___x_5628_);
v___x_5630_ = lean_st_ref_take(v___y_5609_);
v_mctx_5631_ = lean_ctor_get(v___x_5630_, 0);
v_zetaDeltaFVarIds_5632_ = lean_ctor_get(v___x_5630_, 2);
v_postponed_5633_ = lean_ctor_get(v___x_5630_, 3);
v_diag_5634_ = lean_ctor_get(v___x_5630_, 4);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5644_ == 0)
{
lean_object* v_unused_5645_; 
v_unused_5645_ = lean_ctor_get(v___x_5630_, 1);
lean_dec(v_unused_5645_);
v___x_5636_ = v___x_5630_;
v_isShared_5637_ = v_isSharedCheck_5644_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_diag_5634_);
lean_inc(v_postponed_5633_);
lean_inc(v_zetaDeltaFVarIds_5632_);
lean_inc(v_mctx_5631_);
lean_dec(v___x_5630_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5644_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5638_; lean_object* v___x_5640_; 
v___x_5638_ = lean_box(0);
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 1, v___x_5610_);
v___x_5640_ = v___x_5636_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_mctx_5631_);
lean_ctor_set(v_reuseFailAlloc_5643_, 1, v___x_5610_);
lean_ctor_set(v_reuseFailAlloc_5643_, 2, v_zetaDeltaFVarIds_5632_);
lean_ctor_set(v_reuseFailAlloc_5643_, 3, v_postponed_5633_);
lean_ctor_set(v_reuseFailAlloc_5643_, 4, v_diag_5634_);
v___x_5640_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5641_ = lean_st_ref_put(v___y_5609_, v___x_5640_);
v___x_5642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5638_);
return v___x_5642_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5606_ = stack[0].m_obj;
uint8_t v_isExporting_5607_ = stack[1].m_num;
lean_object* v___x_5608_ = stack[2].m_obj;
lean_object* v___y_5609_ = stack[3].m_obj;
lean_object* v___x_5610_ = stack[4].m_obj;
lean_object* v_a_x3f_5611_ = stack[5].m_obj;
lean_object* v_res_5649_;
v_res_5649_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5606_, v_isExporting_5607_, v___x_5608_, v___y_5609_, v___x_5610_, v_a_x3f_5611_);
stack->m_obj
 = v_res_5649_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5650_, lean_object* v_isExporting_5651_, lean_object* v___x_5652_, lean_object* v___y_5653_, lean_object* v___x_5654_, lean_object* v_a_x3f_5655_, lean_object* v___y_5656_){
_start:
{
uint8_t v_isExporting_boxed_5657_; lean_object* v_res_5658_; 
v_isExporting_boxed_5657_ = lean_unbox(v_isExporting_5651_);
v_res_5658_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5650_, v_isExporting_boxed_5657_, v___x_5652_, v___y_5653_, v___x_5654_, v_a_x3f_5655_);
lean_dec(v_a_x3f_5655_);
lean_dec(v___y_5653_);
lean_dec(v___y_5650_);
return v_res_5658_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5659_; lean_object* v___x_5660_; 
v___x_5659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_5660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
return v___x_5660_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5661_; lean_object* v___x_5662_; 
v___x_5661_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
return v___x_5662_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5663_; lean_object* v___x_5664_; 
v___x_5663_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5664_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5663_);
lean_ctor_set(v___x_5664_, 2, v___x_5663_);
lean_ctor_set(v___x_5664_, 3, v___x_5663_);
lean_ctor_set(v___x_5664_, 4, v___x_5663_);
lean_ctor_set(v___x_5664_, 5, v___x_5663_);
return v___x_5664_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5665_, uint8_t v_isExporting_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_){
_start:
{
lean_object* v___x_5672_; lean_object* v_env_5673_; lean_object* v___x_5674_; uint8_t v_isModule_5675_; 
v___x_5672_ = lean_st_ref_get(v___y_5670_);
v_env_5673_ = lean_ctor_get(v___x_5672_, 0);
lean_inc_ref(v_env_5673_);
lean_dec(v___x_5672_);
v___x_5674_ = l_Lean_Environment_header(v_env_5673_);
v_isModule_5675_ = lean_ctor_get_uint8(v___x_5674_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5674_);
if (v_isModule_5675_ == 0)
{
lean_object* v___x_5676_; 
lean_dec_ref(v_env_5673_);
lean_inc(v___y_5670_);
lean_inc_ref(v___y_5669_);
lean_inc(v___y_5668_);
lean_inc_ref(v___y_5667_);
v___x_5676_ = lean_apply_5(v_x_5665_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, lean_box(0));
return v___x_5676_;
}
else
{
uint8_t v_isExporting_5677_; 
v_isExporting_5677_ = lean_ctor_get_uint8(v_env_5673_, sizeof(void*)*13);
lean_dec_ref(v_env_5673_);
if (v_isExporting_5666_ == 0)
{
if (v_isExporting_5677_ == 0)
{
lean_object* v___x_5744_; 
lean_inc(v___y_5670_);
lean_inc_ref(v___y_5669_);
lean_inc(v___y_5668_);
lean_inc_ref(v___y_5667_);
v___x_5744_ = lean_apply_5(v_x_5665_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, lean_box(0));
return v___x_5744_;
}
else
{
goto v___jp_5678_;
}
}
else
{
if (v_isExporting_5677_ == 0)
{
goto v___jp_5678_;
}
else
{
lean_object* v___x_5745_; 
lean_inc(v___y_5670_);
lean_inc_ref(v___y_5669_);
lean_inc(v___y_5668_);
lean_inc_ref(v___y_5667_);
v___x_5745_ = lean_apply_5(v_x_5665_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, lean_box(0));
return v___x_5745_;
}
}
v___jp_5678_:
{
lean_object* v___x_5679_; lean_object* v_env_5680_; lean_object* v_nextMacroScope_5681_; lean_object* v_ngen_5682_; lean_object* v_auxDeclNGen_5683_; lean_object* v_traceState_5684_; lean_object* v_recordedDeps_5685_; lean_object* v_messages_5686_; lean_object* v_infoState_5687_; lean_object* v_snapshotTasks_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5742_; 
v___x_5679_ = lean_st_ref_take(v___y_5670_);
v_env_5680_ = lean_ctor_get(v___x_5679_, 0);
v_nextMacroScope_5681_ = lean_ctor_get(v___x_5679_, 1);
v_ngen_5682_ = lean_ctor_get(v___x_5679_, 2);
v_auxDeclNGen_5683_ = lean_ctor_get(v___x_5679_, 3);
v_traceState_5684_ = lean_ctor_get(v___x_5679_, 4);
v_recordedDeps_5685_ = lean_ctor_get(v___x_5679_, 6);
v_messages_5686_ = lean_ctor_get(v___x_5679_, 7);
v_infoState_5687_ = lean_ctor_get(v___x_5679_, 8);
v_snapshotTasks_5688_ = lean_ctor_get(v___x_5679_, 9);
v_isSharedCheck_5742_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5742_ == 0)
{
lean_object* v_unused_5743_; 
v_unused_5743_ = lean_ctor_get(v___x_5679_, 5);
lean_dec(v_unused_5743_);
v___x_5690_ = v___x_5679_;
v_isShared_5691_ = v_isSharedCheck_5742_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_snapshotTasks_5688_);
lean_inc(v_infoState_5687_);
lean_inc(v_messages_5686_);
lean_inc(v_recordedDeps_5685_);
lean_inc(v_traceState_5684_);
lean_inc(v_auxDeclNGen_5683_);
lean_inc(v_ngen_5682_);
lean_inc(v_nextMacroScope_5681_);
lean_inc(v_env_5680_);
lean_dec(v___x_5679_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5742_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5695_; 
v___x_5692_ = l_Lean_Environment_setExporting(v_env_5680_, v_isExporting_5666_);
v___x_5693_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
if (v_isShared_5691_ == 0)
{
lean_ctor_set(v___x_5690_, 5, v___x_5693_);
lean_ctor_set(v___x_5690_, 0, v___x_5692_);
v___x_5695_ = v___x_5690_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5692_);
lean_ctor_set(v_reuseFailAlloc_5741_, 1, v_nextMacroScope_5681_);
lean_ctor_set(v_reuseFailAlloc_5741_, 2, v_ngen_5682_);
lean_ctor_set(v_reuseFailAlloc_5741_, 3, v_auxDeclNGen_5683_);
lean_ctor_set(v_reuseFailAlloc_5741_, 4, v_traceState_5684_);
lean_ctor_set(v_reuseFailAlloc_5741_, 5, v___x_5693_);
lean_ctor_set(v_reuseFailAlloc_5741_, 6, v_recordedDeps_5685_);
lean_ctor_set(v_reuseFailAlloc_5741_, 7, v_messages_5686_);
lean_ctor_set(v_reuseFailAlloc_5741_, 8, v_infoState_5687_);
lean_ctor_set(v_reuseFailAlloc_5741_, 9, v_snapshotTasks_5688_);
v___x_5695_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v_mctx_5698_; lean_object* v_zetaDeltaFVarIds_5699_; lean_object* v_postponed_5700_; lean_object* v_diag_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5739_; 
v___x_5696_ = lean_st_ref_put(v___y_5670_, v___x_5695_);
v___x_5697_ = lean_st_ref_take(v___y_5668_);
v_mctx_5698_ = lean_ctor_get(v___x_5697_, 0);
v_zetaDeltaFVarIds_5699_ = lean_ctor_get(v___x_5697_, 2);
v_postponed_5700_ = lean_ctor_get(v___x_5697_, 3);
v_diag_5701_ = lean_ctor_get(v___x_5697_, 4);
v_isSharedCheck_5739_ = !lean_is_exclusive(v___x_5697_);
if (v_isSharedCheck_5739_ == 0)
{
lean_object* v_unused_5740_; 
v_unused_5740_ = lean_ctor_get(v___x_5697_, 1);
lean_dec(v_unused_5740_);
v___x_5703_ = v___x_5697_;
v_isShared_5704_ = v_isSharedCheck_5739_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_diag_5701_);
lean_inc(v_postponed_5700_);
lean_inc(v_zetaDeltaFVarIds_5699_);
lean_inc(v_mctx_5698_);
lean_dec(v___x_5697_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5739_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5705_; lean_object* v___x_5707_; 
v___x_5705_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 1, v___x_5705_);
v___x_5707_ = v___x_5703_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5738_; 
v_reuseFailAlloc_5738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5738_, 0, v_mctx_5698_);
lean_ctor_set(v_reuseFailAlloc_5738_, 1, v___x_5705_);
lean_ctor_set(v_reuseFailAlloc_5738_, 2, v_zetaDeltaFVarIds_5699_);
lean_ctor_set(v_reuseFailAlloc_5738_, 3, v_postponed_5700_);
lean_ctor_set(v_reuseFailAlloc_5738_, 4, v_diag_5701_);
v___x_5707_ = v_reuseFailAlloc_5738_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
lean_object* v___x_5708_; lean_object* v_r_5709_; 
v___x_5708_ = lean_st_ref_put(v___y_5668_, v___x_5707_);
lean_inc(v___y_5670_);
lean_inc_ref(v___y_5669_);
lean_inc(v___y_5668_);
lean_inc_ref(v___y_5667_);
v_r_5709_ = lean_apply_5(v_x_5665_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, lean_box(0));
if (lean_obj_tag(v_r_5709_) == 0)
{
lean_object* v_a_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5726_; 
v_a_5710_ = lean_ctor_get(v_r_5709_, 0);
v_isSharedCheck_5726_ = !lean_is_exclusive(v_r_5709_);
if (v_isSharedCheck_5726_ == 0)
{
v___x_5712_ = v_r_5709_;
v_isShared_5713_ = v_isSharedCheck_5726_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_a_5710_);
lean_dec(v_r_5709_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5726_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5715_; 
lean_inc(v_a_5710_);
if (v_isShared_5713_ == 0)
{
lean_ctor_set_tag(v___x_5712_, 1);
v___x_5715_ = v___x_5712_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_a_5710_);
v___x_5715_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
lean_object* v___x_5716_; lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5723_; 
v___x_5716_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5670_, v_isExporting_5677_, v___x_5693_, v___y_5668_, v___x_5705_, v___x_5715_);
lean_dec_ref(v___x_5715_);
v_isSharedCheck_5723_ = !lean_is_exclusive(v___x_5716_);
if (v_isSharedCheck_5723_ == 0)
{
lean_object* v_unused_5724_; 
v_unused_5724_ = lean_ctor_get(v___x_5716_, 0);
lean_dec(v_unused_5724_);
v___x_5718_ = v___x_5716_;
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
else
{
lean_dec(v___x_5716_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
lean_object* v___x_5721_; 
if (v_isShared_5719_ == 0)
{
lean_ctor_set(v___x_5718_, 0, v_a_5710_);
v___x_5721_ = v___x_5718_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5722_; 
v_reuseFailAlloc_5722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_a_5710_);
v___x_5721_ = v_reuseFailAlloc_5722_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
return v___x_5721_;
}
}
}
}
}
else
{
lean_object* v_a_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5736_; 
v_a_5727_ = lean_ctor_get(v_r_5709_, 0);
lean_inc(v_a_5727_);
lean_dec_ref_known(v_r_5709_, 1);
v___x_5728_ = lean_box(0);
v___x_5729_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5670_, v_isExporting_5677_, v___x_5693_, v___y_5668_, v___x_5705_, v___x_5728_);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5736_ == 0)
{
lean_object* v_unused_5737_; 
v_unused_5737_ = lean_ctor_get(v___x_5729_, 0);
lean_dec(v_unused_5737_);
v___x_5731_ = v___x_5729_;
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
else
{
lean_dec(v___x_5729_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5734_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set_tag(v___x_5731_, 1);
lean_ctor_set(v___x_5731_, 0, v_a_5727_);
v___x_5734_ = v___x_5731_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5727_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5665_ = stack[0].m_obj;
uint8_t v_isExporting_5666_ = stack[1].m_num;
lean_object* v___y_5667_ = stack[2].m_obj;
lean_object* v___y_5668_ = stack[3].m_obj;
lean_object* v___y_5669_ = stack[4].m_obj;
lean_object* v___y_5670_ = stack[5].m_obj;
lean_object* v_res_5746_;
v_res_5746_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5665_, v_isExporting_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_);
stack->m_obj
 = v_res_5746_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5747_, lean_object* v_isExporting_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_){
_start:
{
uint8_t v_isExporting_boxed_5754_; lean_object* v_res_5755_; 
v_isExporting_boxed_5754_ = lean_unbox(v_isExporting_5748_);
v_res_5755_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5747_, v_isExporting_boxed_5754_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
lean_dec(v___y_5752_);
lean_dec_ref(v___y_5751_);
lean_dec(v___y_5750_);
lean_dec_ref(v___y_5749_);
return v_res_5755_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5756_, uint8_t v_when_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_){
_start:
{
if (v_when_5757_ == 0)
{
lean_object* v___x_5763_; 
lean_inc(v___y_5761_);
lean_inc_ref(v___y_5760_);
lean_inc(v___y_5759_);
lean_inc_ref(v___y_5758_);
v___x_5763_ = lean_apply_5(v_x_5756_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, lean_box(0));
return v___x_5763_;
}
else
{
uint8_t v___x_5764_; lean_object* v___x_5765_; 
v___x_5764_ = 0;
v___x_5765_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5756_, v___x_5764_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
return v___x_5765_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5756_ = stack[0].m_obj;
uint8_t v_when_5757_ = stack[1].m_num;
lean_object* v___y_5758_ = stack[2].m_obj;
lean_object* v___y_5759_ = stack[3].m_obj;
lean_object* v___y_5760_ = stack[4].m_obj;
lean_object* v___y_5761_ = stack[5].m_obj;
lean_object* v_res_5766_;
v_res_5766_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5756_, v_when_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
stack->m_obj
 = v_res_5766_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5767_, lean_object* v_when_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_){
_start:
{
uint8_t v_when_boxed_5774_; lean_object* v_res_5775_; 
v_when_boxed_5774_ = lean_unbox(v_when_5768_);
v_res_5775_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5767_, v_when_boxed_5774_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
lean_dec(v___y_5772_);
lean_dec_ref(v___y_5771_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
return v_res_5775_;
}
}
lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_){
_start:
{
lean_object* v___x_5782_; lean_object* v_a_5783_; lean_object* v___x_5784_; uint8_t v___x_5785_; lean_object* v___x_5786_; 
v___x_5782_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5776_, v___y_5778_);
v_a_5783_ = lean_ctor_get(v___x_5782_, 0);
lean_inc(v_a_5783_);
lean_dec_ref(v___x_5782_);
v___x_5784_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5784_, 0, v_a_5783_);
v___x_5785_ = 1;
v___x_5786_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5784_, v___x_5785_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_);
return v___x_5786_;
}
}
LEAN_EXPORT void l_Lean_Meta_letToHave___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5776_ = stack[0].m_obj;
lean_object* v___y_5777_ = stack[1].m_obj;
lean_object* v___y_5778_ = stack[2].m_obj;
lean_object* v___y_5779_ = stack[3].m_obj;
lean_object* v___y_5780_ = stack[4].m_obj;
lean_object* v_res_5787_;
v_res_5787_ = l_Lean_Meta_letToHave___lam__0(v_e_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_);
stack->m_obj
 = v_res_5787_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_){
_start:
{
lean_object* v_res_5794_; 
v_res_5794_ = l_Lean_Meta_letToHave___lam__0(v_e_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_);
lean_dec(v___y_5792_);
lean_dec_ref(v___y_5791_);
lean_dec(v___y_5790_);
lean_dec_ref(v___y_5789_);
return v_res_5794_;
}
}
lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_){
_start:
{
lean_object* v___f_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; 
v___f_5802_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5802_, 0, v_e_5796_);
v___x_5803_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5799_);
v___x_5804_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5805_ = lean_box(0);
v___x_5806_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5804_, v___x_5803_, v___f_5802_, v___x_5805_, v_a_5797_, v_a_5798_, v_a_5799_, v_a_5800_);
lean_dec_ref(v___x_5803_);
return v___x_5806_;
}
}
LEAN_EXPORT void l_Lean_Meta_letToHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5796_ = stack[0].m_obj;
lean_object* v_a_5797_ = stack[1].m_obj;
lean_object* v_a_5798_ = stack[2].m_obj;
lean_object* v_a_5799_ = stack[3].m_obj;
lean_object* v_a_5800_ = stack[4].m_obj;
lean_object* v_res_5807_;
v_res_5807_ = l_Lean_Meta_letToHave(v_e_5796_, v_a_5797_, v_a_5798_, v_a_5799_, v_a_5800_);
stack->m_obj
 = v_res_5807_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l_Lean_Meta_letToHave(v_e_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_);
lean_dec(v_a_5812_);
lean_dec_ref(v_a_5811_);
lean_dec(v_a_5810_);
lean_dec_ref(v_a_5809_);
return v_res_5814_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5815_, lean_object* v_x_5816_, uint8_t v_isExporting_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
lean_object* v___x_5823_; 
v___x_5823_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5816_, v_isExporting_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
return v___x_5823_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5816_ = stack[1].m_obj;
uint8_t v_isExporting_5817_ = stack[2].m_num;
lean_object* v___y_5818_ = stack[3].m_obj;
lean_object* v___y_5819_ = stack[4].m_obj;
lean_object* v___y_5820_ = stack[5].m_obj;
lean_object* v___y_5821_ = stack[6].m_obj;
lean_object* v_res_5824_;
v_res_5824_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_box(0), v_x_5816_, v_isExporting_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
stack->m_obj
 = v_res_5824_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5825_, lean_object* v_x_5826_, lean_object* v_isExporting_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_){
_start:
{
uint8_t v_isExporting_boxed_5833_; lean_object* v_res_5834_; 
v_isExporting_boxed_5833_ = lean_unbox(v_isExporting_5827_);
v_res_5834_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5825_, v_x_5826_, v_isExporting_boxed_5833_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_);
lean_dec(v___y_5831_);
lean_dec_ref(v___y_5830_);
lean_dec(v___y_5829_);
lean_dec_ref(v___y_5828_);
return v_res_5834_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5835_, lean_object* v_x_5836_, uint8_t v_when_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_){
_start:
{
lean_object* v___x_5843_; 
v___x_5843_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5836_, v_when_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_);
return v___x_5843_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5836_ = stack[1].m_obj;
uint8_t v_when_5837_ = stack[2].m_num;
lean_object* v___y_5838_ = stack[3].m_obj;
lean_object* v___y_5839_ = stack[4].m_obj;
lean_object* v___y_5840_ = stack[5].m_obj;
lean_object* v___y_5841_ = stack[6].m_obj;
lean_object* v_res_5844_;
v_res_5844_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_box(0), v_x_5836_, v_when_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_);
stack->m_obj
 = v_res_5844_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5845_, lean_object* v_x_5846_, lean_object* v_when_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_){
_start:
{
uint8_t v_when_boxed_5853_; lean_object* v_res_5854_; 
v_when_boxed_5853_ = lean_unbox(v_when_5847_);
v_res_5854_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5845_, v_x_5846_, v_when_boxed_5853_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
return v_res_5854_;
}
}
lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5911_; uint8_t v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5911_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5912_ = 0;
v___x_5913_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5914_ = l_Lean_registerTraceClass(v___x_5911_, v___x_5912_, v___x_5913_);
if (lean_obj_tag(v___x_5914_) == 0)
{
lean_object* v___x_5915_; lean_object* v___x_5916_; 
lean_dec_ref_known(v___x_5914_, 1);
v___x_5915_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5916_ = l_Lean_registerTraceClass(v___x_5915_, v___x_5912_, v___x_5913_);
return v___x_5916_;
}
else
{
return v___x_5914_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5917_;
v_res_5917_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5917_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5918_){
_start:
{
lean_object* v_res_5919_; 
v_res_5919_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5919_;
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
