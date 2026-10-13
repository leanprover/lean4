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
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
lean_ctor_set(v___x_1266_, 2, v___x_1265_);
lean_ctor_set(v___x_1266_, 3, v___x_1265_);
lean_ctor_set(v___x_1266_, 4, v___x_1264_);
lean_ctor_set(v___x_1266_, 5, v___x_1264_);
lean_ctor_set(v___x_1266_, 6, v___x_1264_);
lean_ctor_set(v___x_1266_, 7, v___x_1264_);
lean_ctor_set(v___x_1266_, 8, v___x_1264_);
lean_ctor_set(v___x_1266_, 9, v___x_1264_);
lean_ctor_set(v___x_1266_, 10, v___x_1264_);
lean_ctor_set(v___x_1266_, 11, v___x_1263_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_unsigned_to_nat(32u);
v___x_1268_ = lean_mk_empty_array_with_capacity(v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1270_ = ((size_t)5ULL);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_unsigned_to_nat(32u);
v___x_1273_ = lean_mk_empty_array_with_capacity(v___x_1272_);
v___x_1274_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1275_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1271_);
lean_ctor_set(v___x_1275_, 3, v___x_1271_);
lean_ctor_set_usize(v___x_1275_, 4, v___x_1270_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = lean_box(1);
v___x_1277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1277_);
lean_ctor_set(v___x_1279_, 2, v___x_1276_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__22));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__24));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__26));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1313_, lean_object* v_declHint_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_env_1319_; uint8_t v___x_1320_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_st_ref_get(v___y_1315_);
v_env_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref(v_env_1319_);
lean_dec(v___x_1318_);
v___x_1320_ = l_Lean_Name_isAnonymous(v_declHint_1314_);
if (v___x_1320_ == 0)
{
uint8_t v_isExporting_1321_; 
v_isExporting_1321_ = lean_ctor_get_uint8(v_env_1319_, sizeof(void*)*13);
if (v_isExporting_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec_ref(v_env_1319_);
lean_dec(v_declHint_1314_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_msg_1313_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
lean_inc_ref(v_env_1319_);
v___x_1323_ = l_Lean_Environment_setExporting(v_env_1319_, v___x_1320_);
lean_inc(v_declHint_1314_);
lean_inc_ref(v___x_1323_);
v___x_1324_ = l_Lean_Environment_contains(v___x_1323_, v_declHint_1314_, v_isExporting_1321_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec_ref(v___x_1323_);
lean_dec_ref(v_env_1319_);
lean_dec(v_declHint_1314_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_msg_1313_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_c_1331_; lean_object* v___x_1332_; 
v___x_1326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1327_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1328_ = l_Lean_Options_empty;
v___x_1329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1323_);
lean_ctor_set(v___x_1329_, 1, v___x_1326_);
lean_ctor_set(v___x_1329_, 2, v___x_1327_);
lean_ctor_set(v___x_1329_, 3, v___x_1328_);
lean_inc(v_declHint_1314_);
v___x_1330_ = l_Lean_MessageData_ofConstName(v_declHint_1314_, v___x_1320_);
v_c_1331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1331_, 0, v___x_1329_);
lean_ctor_set(v_c_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1319_, v_declHint_1314_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_env_1319_);
lean_dec(v_declHint_1314_);
v___x_1333_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_c_1331_);
v___x_1335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Lean_MessageData_note(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_msg_1313_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v_val_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1396_; 
v_val_1340_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1342_ = v___x_1332_;
v_isShared_1343_ = v_isSharedCheck_1396_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_val_1340_);
lean_dec(v___x_1332_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1396_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v_modules_1345_; lean_object* v_moduleNames_1346_; lean_object* v_mod_1347_; uint8_t v___y_1349_; uint8_t v___x_1379_; 
v___x_1344_ = l_Lean_Environment_header(v_env_1319_);
lean_dec_ref(v_env_1319_);
v_modules_1345_ = lean_ctor_get(v___x_1344_, 3);
lean_inc_ref(v_modules_1345_);
v_moduleNames_1346_ = lean_ctor_get(v___x_1344_, 4);
lean_inc_ref(v_moduleNames_1346_);
lean_dec_ref(v___x_1344_);
v_mod_1347_ = lean_array_get(v___x_1317_, v_moduleNames_1346_, v_val_1340_);
lean_dec_ref(v_moduleNames_1346_);
v___x_1379_ = l_Lean_isPrivateName(v_declHint_1314_);
lean_dec(v_declHint_1314_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_array_get_size(v_modules_1345_);
v___x_1381_ = lean_nat_dec_lt(v_val_1340_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v_modules_1345_);
lean_dec(v_val_1340_);
v___y_1349_ = v___x_1379_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1382_; lean_object* v_toImport_1383_; uint8_t v_isExported_1384_; 
v___x_1382_ = lean_array_fget(v_modules_1345_, v_val_1340_);
lean_dec(v_val_1340_);
lean_dec_ref(v_modules_1345_);
v_toImport_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref(v_toImport_1383_);
lean_dec(v___x_1382_);
v_isExported_1384_ = lean_ctor_get_uint8(v_toImport_1383_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1383_);
v___y_1349_ = v_isExported_1384_;
goto v___jp_1348_;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v_modules_1345_);
lean_del_object(v___x_1342_);
lean_dec(v_val_1340_);
v___x_1385_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_c_1331_);
v___x_1387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = l_Lean_MessageData_ofName(v_mod_1347_);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = l_Lean_MessageData_note(v___x_1392_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_msg_1313_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
v___jp_1348_:
{
if (v___y_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v_c_1331_);
v___x_1352_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_MessageData_ofName(v_mod_1347_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_MessageData_note(v___x_1357_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_msg_1313_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1359_);
v___x_1361_ = v___x_1342_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_c_1331_);
v___x_1365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = l_Lean_MessageData_ofName(v_mod_1347_);
lean_inc_ref(v___x_1367_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___x_1367_);
v___x_1372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_MessageData_note(v___x_1373_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_msg_1313_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1375_);
v___x_1377_ = v___x_1342_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
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
lean_object* v___x_1397_; 
lean_dec_ref(v_env_1319_);
lean_dec(v_declHint_1314_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_msg_1313_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1398_, lean_object* v_declHint_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1398_, v_declHint_1399_, v___y_1400_);
lean_dec(v___y_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1403_, lean_object* v_declHint_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1422_; 
v___x_1412_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1403_, v_declHint_1404_, v___y_1410_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1417_ = l_Lean_unknownIdentifierMessageTag;
v___x_1418_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v_a_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1418_);
v___x_1420_ = v___x_1415_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1423_, lean_object* v_declHint_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1423_, v_declHint_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec(v___y_1425_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; lean_object* v_env_1440_; uint8_t v___x_1441_; lean_object* v_env_1442_; lean_object* v___x_1443_; lean_object* v_toCold_1444_; lean_object* v_mctx_1445_; lean_object* v_lctx_1446_; lean_object* v_options_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1439_ = lean_st_ref_get(v___y_1437_);
v_env_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc_ref(v_env_1440_);
lean_dec(v___x_1439_);
v___x_1441_ = 0;
v_env_1442_ = l_Lean_Environment_setRecordingDeps(v_env_1440_, v___x_1441_);
v___x_1443_ = lean_st_ref_get(v___y_1435_);
v_toCold_1444_ = lean_ctor_get(v___y_1436_, 0);
v_mctx_1445_ = lean_ctor_get(v___x_1443_, 0);
lean_inc_ref(v_mctx_1445_);
lean_dec(v___x_1443_);
v_lctx_1446_ = lean_ctor_get(v___y_1434_, 2);
v_options_1447_ = lean_ctor_get(v_toCold_1444_, 2);
lean_inc_ref(v_options_1447_);
lean_inc_ref(v_lctx_1446_);
v___x_1448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1448_, 0, v_env_1442_);
lean_ctor_set(v___x_1448_, 1, v_mctx_1445_);
lean_ctor_set(v___x_1448_, 2, v_lctx_1446_);
lean_ctor_set(v___x_1448_, 3, v_options_1447_);
v___x_1449_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v_msgData_1433_);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_ref_1464_; lean_object* v___x_1465_; lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_ref_1464_ = lean_ctor_get(v___y_1461_, 2);
v___x_1465_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
lean_inc(v_ref_1464_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_ref_1464_);
lean_ctor_set(v___x_1470_, 1, v_a_1466_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 1);
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1482_, lean_object* v_msg_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_toCold_1491_; lean_object* v_currRecDepth_1492_; lean_object* v_ref_1493_; uint16_t v_optionFlags_1494_; uint8_t v_suppressElabErrors_1495_; uint8_t v_isRecordingDeps_1496_; lean_object* v_ref_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_toCold_1491_ = lean_ctor_get(v___y_1488_, 0);
v_currRecDepth_1492_ = lean_ctor_get(v___y_1488_, 1);
v_ref_1493_ = lean_ctor_get(v___y_1488_, 2);
v_optionFlags_1494_ = lean_ctor_get_uint16(v___y_1488_, sizeof(void*)*3);
v_suppressElabErrors_1495_ = lean_ctor_get_uint8(v___y_1488_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1496_ = lean_ctor_get_uint8(v___y_1488_, sizeof(void*)*3 + 3);
v_ref_1497_ = l_Lean_replaceRef(v_ref_1482_, v_ref_1493_);
lean_inc(v_currRecDepth_1492_);
lean_inc_ref(v_toCold_1491_);
v___x_1498_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1498_, 0, v_toCold_1491_);
lean_ctor_set(v___x_1498_, 1, v_currRecDepth_1492_);
lean_ctor_set(v___x_1498_, 2, v_ref_1497_);
lean_ctor_set_uint16(v___x_1498_, sizeof(void*)*3, v_optionFlags_1494_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*3 + 2, v_suppressElabErrors_1495_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*3 + 3, v_isRecordingDeps_1496_);
v___x_1499_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1483_, v___y_1486_, v___y_1487_, v___x_1498_, v___y_1489_);
lean_dec_ref_known(v___x_1498_, 3);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1500_, v_msg_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec(v_ref_1500_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1510_, lean_object* v_msg_1511_, lean_object* v_declHint_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v_a_1521_; lean_object* v___x_1522_; 
v___x_1520_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1511_, v_declHint_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1510_, v_a_1521_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v_declHint_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1523_, v_msg_1524_, v_declHint_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec(v_ref_1523_);
return v_res_1533_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1540_, lean_object* v_constName_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1549_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1550_ = 0;
lean_inc(v_constName_1541_);
v___x_1551_ = l_Lean_MessageData_ofConstName(v_constName_1541_, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1549_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1540_, v___x_1554_, v_constName_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1556_, lean_object* v_constName_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1556_, v_constName_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v_ref_1556_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_ref_1574_; lean_object* v___x_1575_; 
v_ref_1574_ = lean_ctor_get(v___y_1571_, 2);
v___x_1575_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1574_, v_constName_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec(v___y_1577_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v_env_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_st_ref_get(v___y_1591_);
v_env_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc_ref(v_env_1594_);
lean_dec(v___x_1593_);
v___x_1595_ = 0;
lean_inc(v_constName_1585_);
v___x_1596_ = l_Lean_Environment_findConstVal_x3f(v_env_1594_, v_constName_1585_, v___x_1595_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1597_;
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_constName_1585_);
v_val_1598_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1596_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v___x_1596_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_val_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec(v___y_1607_);
return v_res_1614_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1619_ = lean_unsigned_to_nat(35u);
v___x_1620_ = lean_unsigned_to_nat(203u);
v___x_1621_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1623_ = l_mkPanicMessageWithDecl(v___x_1622_, v___x_1621_, v___x_1620_, v___x_1619_, v___x_1618_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
if (lean_obj_tag(v_e_1624_) == 4)
{
lean_object* v_declName_1632_; lean_object* v_us_1633_; lean_object* v___x_1634_; 
v_declName_1632_ = lean_ctor_get(v_e_1624_, 0);
v_us_1633_ = lean_ctor_get(v_e_1624_, 1);
lean_inc(v_declName_1632_);
v___x_1634_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1632_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_levelParams_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v_levelParams_1636_ = lean_ctor_get(v_a_1635_, 1);
v___x_1637_ = l_List_lengthTR___redArg(v_levelParams_1636_);
v___x_1638_ = l_List_lengthTR___redArg(v_us_1633_);
v___x_1639_ = lean_nat_dec_eq(v___x_1637_, v___x_1638_);
lean_dec(v___x_1638_);
lean_dec(v___x_1637_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_inc(v_us_1633_);
lean_inc(v_declName_1632_);
lean_dec(v_a_1635_);
lean_dec_ref_known(v_e_1624_, 2);
v___x_1640_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1632_, v_us_1633_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; 
lean_inc(v_us_1633_);
v___x_1641_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1635_, v_us_1633_, v___y_1630_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1651_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_a_1642_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_e_1624_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1647_);
v___x_1649_ = v___x_1644_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref_known(v_e_1624_, 2);
v_a_1652_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1641_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1641_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref_known(v_e_1624_, 2);
v_a_1660_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1634_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1634_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v_e_1624_);
v___x_1668_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1669_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1668_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___y_1687_; lean_object* v___x_1688_; 
lean_inc_ref(v_e_1679_);
v___y_1687_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1687_, 0, v_e_1679_);
v___x_1688_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1679_, v___y_1687_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec(v_a_1690_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1698_, lean_object* v_constName_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_constName_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1708_, v_constName_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1718_, lean_object* v_ref_1719_, lean_object* v_constName_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1719_, v_constName_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_ref_1730_, lean_object* v_constName_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1729_, v_ref_1730_, v_constName_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec(v_ref_1730_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1740_, lean_object* v_ref_1741_, lean_object* v_msg_1742_, lean_object* v_declHint_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1741_, v_msg_1742_, v_declHint_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_ref_1753_, lean_object* v_msg_1754_, lean_object* v_declHint_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1752_, v_ref_1753_, v_msg_1754_, v_declHint_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec(v_ref_1753_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1764_, lean_object* v_declHint_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1764_, v_declHint_1765_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1774_, lean_object* v_declHint_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1774_, v_declHint_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1784_, lean_object* v_ref_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1785_, v_msg_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_ref_1796_, lean_object* v_msg_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1795_, v_ref_1796_, v_msg_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec(v_ref_1796_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1806_, lean_object* v_msg_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1807_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1816_, lean_object* v_msg_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1816_, v_msg_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec(v___y_1818_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1827_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_r_1826_);
return v___x_1835_;
}
else
{
lean_object* v___x_1836_; 
lean_inc_ref(v_r_1826_);
v___x_1836_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1826_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1889_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1889_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1889_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_expr_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1887_; 
v_expr_1841_ = lean_ctor_get(v_r_1826_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_r_1826_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_r_1826_, 1);
lean_dec(v_unused_1888_);
v___x_1843_ = v_r_1826_;
v_isShared_1844_ = v_isSharedCheck_1887_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_expr_1841_);
lean_dec(v_r_1826_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1887_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Expr_isSort(v_a_1837_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_del_object(v___x_1839_);
lean_inc(v_a_1832_);
lean_inc_ref(v_a_1831_);
lean_inc(v_a_1830_);
lean_inc_ref(v_a_1829_);
v___x_1846_ = lean_whnf(v_a_1837_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1871_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1871_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1871_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
if (lean_obj_tag(v_a_1847_) == 3)
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_a_1847_);
lean_inc_ref(v_expr_1841_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1851_);
v___x_1853_ = v___x_1843_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_expr_1841_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v_count_1855_; lean_object* v_results_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1868_; 
v___x_1854_ = lean_st_ref_take(v_a_1828_);
v_count_1855_ = lean_ctor_get(v___x_1854_, 0);
v_results_1856_ = lean_ctor_get(v___x_1854_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1858_ = v___x_1854_;
v_isShared_1859_ = v_isSharedCheck_1868_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_results_1856_);
lean_inc(v_count_1855_);
lean_dec(v___x_1854_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1868_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_inc_ref(v___x_1853_);
v___x_1860_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1856_, v_expr_1841_, v___x_1853_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_count_1855_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = lean_st_ref_put(v_a_1828_, v___x_1862_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1853_);
v___x_1865_ = v___x_1849_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1853_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
lean_object* v___x_1870_; 
lean_del_object(v___x_1849_);
lean_dec(v_a_1847_);
lean_del_object(v___x_1843_);
v___x_1870_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1841_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1870_;
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_del_object(v___x_1843_);
lean_dec_ref(v_expr_1841_);
v_a_1872_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1846_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1846_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1837_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1880_);
v___x_1882_ = v___x_1843_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_expr_1841_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1882_);
v___x_1884_ = v___x_1839_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_r_1826_);
v_a_1890_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1836_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1836_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec(v_a_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1907_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = l_Lean_instInhabitedExpr;
v___x_1909_ = lean_panic_fn_borrowed(v___x_1908_, v_msg_1907_);
return v___x_1909_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1913_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1914_ = lean_unsigned_to_nat(18u);
v___x_1915_ = lean_unsigned_to_nat(1864u);
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1917_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1918_ = l_mkPanicMessageWithDecl(v___x_1917_, v___x_1916_, v___x_1915_, v___x_1914_, v___x_1913_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1919_, lean_object* v_f_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___y_1930_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1943_; lean_object* v_fType_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; uint8_t v___x_2004_; 
v___x_2004_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1922_);
if (v___x_2004_ == 0)
{
if (lean_obj_tag(v_e_1919_) == 5)
{
lean_object* v_expr_2005_; lean_object* v_expr_2006_; lean_object* v_fn_2007_; lean_object* v_arg_2008_; size_t v___x_2009_; size_t v___x_2010_; uint8_t v___x_2011_; 
v_expr_2005_ = lean_ctor_get(v_f_1920_, 0);
lean_inc_ref(v_expr_2005_);
lean_dec_ref(v_f_1920_);
v_expr_2006_ = lean_ctor_get(v_a_1921_, 0);
lean_inc_ref(v_expr_2006_);
lean_dec_ref(v_a_1921_);
v_fn_2007_ = lean_ctor_get(v_e_1919_, 0);
v_arg_2008_ = lean_ctor_get(v_e_1919_, 1);
v___x_2009_ = lean_ptr_addr(v_fn_2007_);
v___x_2010_ = lean_ptr_addr(v_expr_2005_);
v___x_2011_ = lean_usize_dec_eq(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref_known(v_e_1919_, 2);
v___x_2012_ = l_Lean_Expr_app___override(v_expr_2005_, v_expr_2006_);
v___y_1930_ = v___x_2012_;
goto v___jp_1929_;
}
else
{
size_t v___x_2013_; size_t v___x_2014_; uint8_t v___x_2015_; 
v___x_2013_ = lean_ptr_addr(v_arg_2008_);
v___x_2014_ = lean_ptr_addr(v_expr_2006_);
v___x_2015_ = lean_usize_dec_eq(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref_known(v_e_1919_, 2);
v___x_2016_ = l_Lean_Expr_app___override(v_expr_2005_, v_expr_2006_);
v___y_1930_ = v___x_2016_;
goto v___jp_1929_;
}
else
{
lean_dec_ref(v_expr_2006_);
lean_dec_ref(v_expr_2005_);
v___y_1930_ = v_e_1919_;
goto v___jp_1929_;
}
}
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_e_1919_);
v___x_2017_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_2018_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2017_);
v___y_1930_ = v___x_2018_;
goto v___jp_1929_;
}
}
else
{
lean_object* v___x_2019_; 
lean_inc_ref(v_f_1920_);
v___x_2019_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1920_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; uint8_t v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l_Lean_Expr_isForall(v_a_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_inc(v_a_1927_);
lean_inc_ref(v_a_1926_);
lean_inc(v_a_1925_);
lean_inc_ref(v_a_1924_);
v___x_2022_ = lean_whnf(v_a_2020_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v_fType_1960_ = v_a_2023_;
v___y_1961_ = v_a_1923_;
v___y_1962_ = v_a_1924_;
v___y_1963_ = v_a_1925_;
v___y_1964_ = v_a_1926_;
v___y_1965_ = v_a_1927_;
goto v___jp_1959_;
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_e_1919_);
v_a_2024_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2022_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2022_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
v_fType_1960_ = v_a_2020_;
v___y_1961_ = v_a_1923_;
v___y_1962_ = v_a_1924_;
v___y_1963_ = v_a_1925_;
v___y_1964_ = v_a_1926_;
v___y_1965_ = v_a_1927_;
goto v___jp_1959_;
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_e_1919_);
v_a_2032_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2019_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2019_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
v___jp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___y_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
v___jp_1934_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1938_ = lean_expr_instantiate1(v___y_1935_, v___y_1936_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v___y_1935_);
v___x_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___y_1937_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
v___jp_1942_:
{
if (lean_obj_tag(v_e_1919_) == 5)
{
lean_object* v_expr_1944_; lean_object* v_expr_1945_; lean_object* v_fn_1946_; lean_object* v_arg_1947_; size_t v___x_1948_; size_t v___x_1949_; uint8_t v___x_1950_; 
v_expr_1944_ = lean_ctor_get(v_f_1920_, 0);
lean_inc_ref(v_expr_1944_);
lean_dec_ref(v_f_1920_);
v_expr_1945_ = lean_ctor_get(v_a_1921_, 0);
lean_inc_ref(v_expr_1945_);
lean_dec_ref(v_a_1921_);
v_fn_1946_ = lean_ctor_get(v_e_1919_, 0);
v_arg_1947_ = lean_ctor_get(v_e_1919_, 1);
v___x_1948_ = lean_ptr_addr(v_fn_1946_);
v___x_1949_ = lean_ptr_addr(v_expr_1944_);
v___x_1950_ = lean_usize_dec_eq(v___x_1948_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec_ref_known(v_e_1919_, 2);
lean_inc_ref(v_expr_1945_);
v___x_1951_ = l_Lean_Expr_app___override(v_expr_1944_, v_expr_1945_);
v___y_1935_ = v___y_1943_;
v___y_1936_ = v_expr_1945_;
v___y_1937_ = v___x_1951_;
goto v___jp_1934_;
}
else
{
size_t v___x_1952_; size_t v___x_1953_; uint8_t v___x_1954_; 
v___x_1952_ = lean_ptr_addr(v_arg_1947_);
v___x_1953_ = lean_ptr_addr(v_expr_1945_);
v___x_1954_ = lean_usize_dec_eq(v___x_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; 
lean_dec_ref_known(v_e_1919_, 2);
lean_inc_ref(v_expr_1945_);
v___x_1955_ = l_Lean_Expr_app___override(v_expr_1944_, v_expr_1945_);
v___y_1935_ = v___y_1943_;
v___y_1936_ = v_expr_1945_;
v___y_1937_ = v___x_1955_;
goto v___jp_1934_;
}
else
{
lean_dec_ref(v_expr_1944_);
v___y_1935_ = v___y_1943_;
v___y_1936_ = v_expr_1945_;
v___y_1937_ = v_e_1919_;
goto v___jp_1934_;
}
}
}
else
{
lean_object* v_expr_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_e_1919_);
v_expr_1956_ = lean_ctor_get(v_a_1921_, 0);
lean_inc_ref(v_expr_1956_);
lean_dec_ref(v_a_1921_);
v___x_1957_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1958_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1957_);
v___y_1935_ = v___y_1943_;
v___y_1936_ = v_expr_1956_;
v___y_1937_ = v___x_1958_;
goto v___jp_1934_;
}
}
v___jp_1959_:
{
if (lean_obj_tag(v_fType_1960_) == 7)
{
lean_object* v_binderType_1966_; lean_object* v_body_1967_; lean_object* v___x_1968_; 
v_binderType_1966_ = lean_ctor_get(v_fType_1960_, 1);
lean_inc_ref(v_binderType_1966_);
v_body_1967_ = lean_ctor_get(v_fType_1960_, 2);
lean_inc_ref(v_body_1967_);
lean_dec_ref_known(v_fType_1960_, 3);
lean_inc_ref(v_a_1921_);
v___x_1968_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1921_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = l_Lean_Meta_isExprDefEq(v_binderType_1966_, v_a_1969_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; uint8_t v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = lean_unbox(v_a_1971_);
lean_dec(v_a_1971_);
if (v___x_1972_ == 0)
{
lean_object* v_expr_1973_; lean_object* v_expr_1974_; lean_object* v___x_1975_; 
v_expr_1973_ = lean_ctor_get(v_f_1920_, 0);
v_expr_1974_ = lean_ctor_get(v_a_1921_, 0);
lean_inc_ref(v_expr_1974_);
lean_inc_ref(v_expr_1973_);
v___x_1975_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1973_, v_expr_1974_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_dec_ref_known(v___x_1975_, 1);
v___y_1943_ = v_body_1967_;
goto v___jp_1942_;
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v_body_1967_);
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_e_1919_);
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
v___y_1943_ = v_body_1967_;
goto v___jp_1942_;
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_body_1967_);
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_e_1919_);
v_a_1984_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1970_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1970_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v_body_1967_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_e_1919_);
v_a_1992_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1968_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1968_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_expr_2000_; lean_object* v_expr_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec_ref(v_fType_1960_);
lean_dec_ref(v_e_1919_);
v_expr_2000_ = lean_ctor_get(v_f_1920_, 0);
lean_inc_ref(v_expr_2000_);
lean_dec_ref(v_f_1920_);
v_expr_2001_ = lean_ctor_get(v_a_1921_, 0);
lean_inc_ref(v_expr_2001_);
lean_dec_ref(v_a_1921_);
v___x_2002_ = l_Lean_Expr_app___override(v_expr_2000_, v_expr_2001_);
v___x_2003_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_2002_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2040_, lean_object* v_f_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2040_, v_f_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec(v_a_2043_);
return v_res_2050_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2053_ = lean_unsigned_to_nat(37u);
v___x_2054_ = lean_unsigned_to_nat(345u);
v___x_2055_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2056_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2057_ = l_mkPanicMessageWithDecl(v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_, v___x_2052_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2058_, lean_object* v_i_2059_, lean_object* v_a_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_zero_2068_; uint8_t v_isZero_2069_; 
v_zero_2068_ = lean_unsigned_to_nat(0u);
v_isZero_2069_ = lean_nat_dec_eq(v_i_2059_, v_zero_2068_);
if (v_isZero_2069_ == 1)
{
lean_object* v___x_2070_; 
lean_dec(v_i_2059_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_a_2060_);
return v___x_2070_;
}
else
{
lean_object* v_one_2071_; lean_object* v_n_2072_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2083_; lean_object* v___x_2086_; 
v_one_2071_ = lean_unsigned_to_nat(1u);
v_n_2072_ = lean_nat_sub(v_i_2059_, v_one_2071_);
lean_dec(v_i_2059_);
v___x_2086_ = lean_array_fget_borrowed(v_fvars_2058_, v_n_2072_);
if (lean_obj_tag(v___x_2086_) == 1)
{
lean_object* v_fvarId_2087_; lean_object* v___x_2088_; 
v_fvarId_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_fvarId_2087_);
v___x_2088_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2087_, v___y_2063_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
if (lean_obj_tag(v_a_2089_) == 1)
{
lean_object* v_val_2090_; 
v_val_2090_ = lean_ctor_get(v_a_2089_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v_a_2089_, 1);
if (lean_obj_tag(v_val_2090_) == 0)
{
lean_object* v_userName_2091_; lean_object* v_type_2092_; uint8_t v_bi_2093_; lean_object* v_expr_2094_; lean_object* v_type_x3f_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2116_; 
v_userName_2091_ = lean_ctor_get(v_val_2090_, 2);
lean_inc(v_userName_2091_);
v_type_2092_ = lean_ctor_get(v_val_2090_, 3);
lean_inc_ref(v_type_2092_);
v_bi_2093_ = lean_ctor_get_uint8(v_val_2090_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2090_, 4);
v_expr_2094_ = lean_ctor_get(v_a_2060_, 0);
v_type_x3f_2095_ = lean_ctor_get(v_a_2060_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_a_2060_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2097_ = v_a_2060_;
v_isShared_2098_ = v_isSharedCheck_2116_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_type_x3f_2095_);
lean_inc(v_expr_2094_);
lean_dec(v_a_2060_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2116_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___y_2102_; 
v___x_2099_ = lean_expr_abstract_range(v_type_2092_, v_n_2072_, v_fvars_2058_);
lean_dec_ref(v_type_2092_);
lean_inc_ref(v___x_2099_);
lean_inc(v_userName_2091_);
v___x_2100_ = l_Lean_Expr_lam___override(v_userName_2091_, v___x_2099_, v_expr_2094_, v_bi_2093_);
if (lean_obj_tag(v_type_x3f_2095_) == 0)
{
lean_dec_ref(v___x_2099_);
lean_dec(v_userName_2091_);
v___y_2102_ = v_type_x3f_2095_;
goto v___jp_2101_;
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2115_; 
v_val_2107_ = lean_ctor_get(v_type_x3f_2095_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_type_x3f_2095_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2109_ = v_type_x3f_2095_;
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_val_2107_);
lean_dec(v_type_x3f_2095_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = l_Lean_Expr_forallE___override(v_userName_2091_, v___x_2099_, v_val_2107_, v_bi_2093_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
v___y_2102_ = v___x_2113_;
goto v___jp_2101_;
}
}
}
v___jp_2101_:
{
lean_object* v___x_2104_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___y_2102_);
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2104_ = v___x_2097_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___y_2102_);
v___x_2104_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v_i_2059_ = v_n_2072_;
v_a_2060_ = v___x_2104_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2117_; lean_object* v_type_2118_; lean_object* v_value_2119_; uint8_t v_nondep_2120_; uint8_t v_nondep_2122_; lean_object* v___x_2132_; 
v_userName_2117_ = lean_ctor_get(v_val_2090_, 2);
lean_inc(v_userName_2117_);
v_type_2118_ = lean_ctor_get(v_val_2090_, 3);
lean_inc_ref(v_type_2118_);
v_value_2119_ = lean_ctor_get(v_val_2090_, 4);
lean_inc_ref(v_value_2119_);
v_nondep_2120_ = lean_ctor_get_uint8(v_val_2090_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2090_, 5);
v___x_2132_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2064_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; uint8_t v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = 1;
if (v_nondep_2120_ == 0)
{
uint8_t v___x_2135_; 
v___x_2135_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2087_, v_a_2133_);
lean_dec(v_a_2133_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2062_);
lean_dec_ref(v___x_2136_);
v_nondep_2122_ = v___x_2134_;
goto v___jp_2121_;
}
else
{
v_nondep_2122_ = v_nondep_2120_;
goto v___jp_2121_;
}
}
else
{
lean_dec(v_a_2133_);
v_nondep_2122_ = v___x_2134_;
goto v___jp_2121_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_value_2119_);
lean_dec_ref(v_type_2118_);
lean_dec(v_userName_2117_);
lean_dec(v_n_2072_);
lean_dec_ref(v_a_2060_);
v_a_2137_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2132_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
v___jp_2121_:
{
lean_object* v_expr_2123_; lean_object* v_type_x3f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_expr_2123_ = lean_ctor_get(v_a_2060_, 0);
lean_inc_ref(v_expr_2123_);
v_type_x3f_2124_ = lean_ctor_get(v_a_2060_, 1);
lean_inc(v_type_x3f_2124_);
lean_dec_ref(v_a_2060_);
v___x_2125_ = lean_expr_abstract_range(v_type_2118_, v_n_2072_, v_fvars_2058_);
lean_dec_ref(v_type_2118_);
v___x_2126_ = lean_expr_abstract_range(v_value_2119_, v_n_2072_, v_fvars_2058_);
lean_dec_ref(v_value_2119_);
lean_inc_ref(v___x_2126_);
lean_inc_ref(v___x_2125_);
lean_inc(v_userName_2117_);
v___x_2127_ = l_Lean_Expr_letE___override(v_userName_2117_, v___x_2125_, v___x_2126_, v_expr_2123_, v_nondep_2122_);
if (lean_obj_tag(v_type_x3f_2124_) == 0)
{
lean_dec_ref(v___x_2126_);
lean_dec_ref(v___x_2125_);
lean_dec(v_userName_2117_);
v___y_2074_ = v___x_2127_;
v___y_2075_ = v_type_x3f_2124_;
goto v___jp_2073_;
}
else
{
lean_object* v_val_2128_; uint8_t v___x_2129_; 
v_val_2128_ = lean_ctor_get(v_type_x3f_2124_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v_type_x3f_2124_, 1);
v___x_2129_ = lean_expr_has_loose_bvar(v_val_2128_, v_zero_2068_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
lean_dec_ref(v___x_2126_);
lean_dec_ref(v___x_2125_);
lean_dec(v_userName_2117_);
v___x_2130_ = lean_expr_lower_loose_bvars(v_val_2128_, v_one_2071_, v_one_2071_);
lean_dec(v_val_2128_);
v___y_2079_ = v___x_2127_;
v___y_2080_ = v___x_2130_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_Expr_letE___override(v_userName_2117_, v___x_2125_, v___x_2126_, v_val_2128_, v_nondep_2122_);
v___y_2079_ = v___x_2127_;
v___y_2080_ = v___x_2131_;
goto v___jp_2078_;
}
}
}
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2060_);
lean_inc(v_fvarId_2087_);
v___x_2145_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2087_, v___y_2065_, v___y_2066_);
v___y_2083_ = v___x_2145_;
goto v___jp_2082_;
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_n_2072_);
lean_dec_ref(v_a_2060_);
v_a_2146_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2088_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2088_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v_a_2060_);
v___x_2154_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2155_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2154_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v___y_2083_ = v___x_2155_;
goto v___jp_2082_;
}
v___jp_2073_:
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___y_2074_);
lean_ctor_set(v___x_2076_, 1, v___y_2075_);
v_i_2059_ = v_n_2072_;
v_a_2060_ = v___x_2076_;
goto _start;
}
v___jp_2078_:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___y_2080_);
v___y_2074_ = v___y_2079_;
v___y_2075_ = v___x_2081_;
goto v___jp_2073_;
}
v___jp_2082_:
{
if (lean_obj_tag(v___y_2083_) == 0)
{
lean_object* v_a_2084_; 
v_a_2084_ = lean_ctor_get(v___y_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___y_2083_, 1);
v_i_2059_ = v_n_2072_;
v_a_2060_ = v_a_2084_;
goto _start;
}
else
{
lean_dec(v_n_2072_);
return v___y_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2156_, lean_object* v_i_2157_, lean_object* v_a_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2156_, v_i_2157_, v_a_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v_fvars_2156_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
if (lean_obj_tag(v_a_2167_) == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = l_List_reverse___redArg(v_a_2168_);
return v___x_2169_;
}
else
{
lean_object* v_head_2170_; lean_object* v_tail_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2180_; 
v_head_2170_ = lean_ctor_get(v_a_2167_, 0);
v_tail_2171_ = lean_ctor_get(v_a_2167_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_a_2167_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2173_ = v_a_2167_;
v_isShared_2174_ = v_isSharedCheck_2180_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_tail_2171_);
lean_inc(v_head_2170_);
lean_dec(v_a_2167_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2180_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = l_Lean_MessageData_ofExpr(v_head_2170_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_a_2168_);
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2177_ = v___x_2173_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_a_2168_);
v___x_2177_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
v_a_2167_ = v_tail_2171_;
v_a_2168_ = v___x_2177_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2181_; double v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_float_of_nat(v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_ref_2193_; lean_object* v___x_2194_; lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2240_; 
v_ref_2193_ = lean_ctor_get(v___y_2190_, 2);
v___x_2194_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2240_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2240_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v_traceState_2200_; lean_object* v_env_2201_; lean_object* v_nextMacroScope_2202_; lean_object* v_ngen_2203_; lean_object* v_auxDeclNGen_2204_; lean_object* v_cache_2205_; lean_object* v_recordedDeps_2206_; lean_object* v_messages_2207_; lean_object* v_infoState_2208_; lean_object* v_snapshotTasks_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2239_; 
v___x_2199_ = lean_st_ref_take(v___y_2191_);
v_traceState_2200_ = lean_ctor_get(v___x_2199_, 4);
v_env_2201_ = lean_ctor_get(v___x_2199_, 0);
v_nextMacroScope_2202_ = lean_ctor_get(v___x_2199_, 1);
v_ngen_2203_ = lean_ctor_get(v___x_2199_, 2);
v_auxDeclNGen_2204_ = lean_ctor_get(v___x_2199_, 3);
v_cache_2205_ = lean_ctor_get(v___x_2199_, 5);
v_recordedDeps_2206_ = lean_ctor_get(v___x_2199_, 6);
v_messages_2207_ = lean_ctor_get(v___x_2199_, 7);
v_infoState_2208_ = lean_ctor_get(v___x_2199_, 8);
v_snapshotTasks_2209_ = lean_ctor_get(v___x_2199_, 9);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2211_ = v___x_2199_;
v_isShared_2212_ = v_isSharedCheck_2239_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_snapshotTasks_2209_);
lean_inc(v_infoState_2208_);
lean_inc(v_messages_2207_);
lean_inc(v_recordedDeps_2206_);
lean_inc(v_cache_2205_);
lean_inc(v_traceState_2200_);
lean_inc(v_auxDeclNGen_2204_);
lean_inc(v_ngen_2203_);
lean_inc(v_nextMacroScope_2202_);
lean_inc(v_env_2201_);
lean_dec(v___x_2199_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2239_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
uint64_t v_tid_2213_; lean_object* v_traces_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2238_; 
v_tid_2213_ = lean_ctor_get_uint64(v_traceState_2200_, sizeof(void*)*1);
v_traces_2214_ = lean_ctor_get(v_traceState_2200_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_traceState_2200_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2216_ = v_traceState_2200_;
v_isShared_2217_ = v_isSharedCheck_2238_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_traces_2214_);
lean_dec(v_traceState_2200_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2238_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; double v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2221_ = 0;
v___x_2222_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2223_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2223_, 0, v_cls_2186_);
lean_ctor_set(v___x_2223_, 1, v___x_2219_);
lean_ctor_set(v___x_2223_, 2, v___x_2222_);
lean_ctor_set_float(v___x_2223_, sizeof(void*)*3, v___x_2220_);
lean_ctor_set_float(v___x_2223_, sizeof(void*)*3 + 8, v___x_2220_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*3 + 16, v___x_2221_);
v___x_2224_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2225_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v_a_2195_);
lean_ctor_set(v___x_2225_, 2, v___x_2224_);
lean_inc(v_ref_2193_);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_ref_2193_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_PersistentArray_push___redArg(v_traces_2214_, v___x_2226_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2227_);
v___x_2229_ = v___x_2216_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2227_);
lean_ctor_set_uint64(v_reuseFailAlloc_2237_, sizeof(void*)*1, v_tid_2213_);
v___x_2229_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2231_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 4, v___x_2229_);
v___x_2231_ = v___x_2211_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_env_2201_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_nextMacroScope_2202_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_ngen_2203_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_auxDeclNGen_2204_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2236_, 5, v_cache_2205_);
lean_ctor_set(v_reuseFailAlloc_2236_, 6, v_recordedDeps_2206_);
lean_ctor_set(v_reuseFailAlloc_2236_, 7, v_messages_2207_);
lean_ctor_set(v_reuseFailAlloc_2236_, 8, v_infoState_2208_);
lean_ctor_set(v_reuseFailAlloc_2236_, 9, v_snapshotTasks_2209_);
v___x_2231_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_st_ref_put(v___y_2191_, v___x_2231_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2218_);
v___x_2234_ = v___x_2197_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2218_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2241_, lean_object* v_msg_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2241_, v_msg_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2248_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_cls_2259_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2260_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2261_ = l_Lean_Name_append(v___x_2260_, v_cls_2259_);
return v___x_2261_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2264_ = l_Lean_stringToMessageData(v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2275_ = l_Lean_MessageData_ofFormat(v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2276_, lean_object* v_body_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v_toCold_2316_; lean_object* v_options_2317_; uint8_t v_hasTrace_2318_; 
v_toCold_2316_ = lean_ctor_get(v_a_2282_, 0);
v_options_2317_ = lean_ctor_get(v_toCold_2316_, 2);
v_hasTrace_2318_ = lean_ctor_get_uint8(v_options_2317_, sizeof(void*)*1);
if (v_hasTrace_2318_ == 0)
{
v___y_2298_ = v_a_2278_;
v___y_2299_ = v_a_2279_;
v___y_2300_ = v_a_2280_;
v___y_2301_ = v_a_2281_;
v___y_2302_ = v_a_2282_;
v___y_2303_ = v_a_2283_;
goto v___jp_2297_;
}
else
{
lean_object* v_inheritedTraceOptions_2319_; lean_object* v_cls_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v_inheritedTraceOptions_2319_ = lean_ctor_get(v_toCold_2316_, 11);
v_cls_2320_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2321_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2322_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2319_, v_options_2317_, v___x_2321_);
if (v___x_2322_ == 0)
{
v___y_2298_ = v_a_2278_;
v___y_2299_ = v_a_2279_;
v___y_2300_ = v_a_2280_;
v___y_2301_ = v_a_2281_;
v___y_2302_ = v_a_2282_;
v___y_2303_ = v_a_2283_;
goto v___jp_2297_;
}
else
{
lean_object* v_expr_2323_; lean_object* v_type_x3f_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___y_2337_; 
v_expr_2323_ = lean_ctor_get(v_body_2277_, 0);
v_type_x3f_2324_ = lean_ctor_get(v_body_2277_, 1);
v___x_2325_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2276_);
v___x_2326_ = lean_array_to_list(v_fvars_2276_);
v___x_2327_ = lean_box(0);
v___x_2328_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2326_, v___x_2327_);
v___x_2329_ = l_Lean_MessageData_ofList(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2325_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
lean_inc_ref(v_expr_2323_);
v___x_2333_ = l_Lean_MessageData_ofExpr(v_expr_2323_);
v___x_2334_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
if (lean_obj_tag(v_type_x3f_2324_) == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2337_ = v___x_2350_;
goto v___jp_2336_;
}
else
{
lean_object* v_val_2351_; lean_object* v___x_2352_; 
v_val_2351_ = lean_ctor_get(v_type_x3f_2324_, 0);
lean_inc(v_val_2351_);
v___x_2352_ = l_Lean_MessageData_ofExpr(v_val_2351_);
v___y_2337_ = v___x_2352_;
goto v___jp_2336_;
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v___y_2337_);
v___x_2339_ = l_Lean_indentD(v___x_2338_);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2332_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2320_, v___x_2340_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_dec_ref_known(v___x_2341_, 1);
v___y_2298_ = v_a_2278_;
v___y_2299_ = v_a_2279_;
v___y_2300_ = v_a_2280_;
v___y_2301_ = v_a_2281_;
v___y_2302_ = v_a_2282_;
v___y_2303_ = v_a_2283_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v_body_2277_);
lean_dec_ref(v_fvars_2276_);
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
v___jp_2285_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___y_2289_);
lean_ctor_set(v___x_2294_, 1, v___y_2293_);
v___x_2295_ = lean_array_get_size(v_fvars_2276_);
v___x_2296_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2276_, v___x_2295_, v___x_2294_, v___y_2292_, v___y_2291_, v___y_2287_, v___y_2286_, v___y_2288_, v___y_2290_);
lean_dec_ref(v_fvars_2276_);
return v___x_2296_;
}
v___jp_2297_:
{
lean_object* v_expr_2304_; lean_object* v_type_x3f_2305_; lean_object* v___x_2306_; 
v_expr_2304_ = lean_ctor_get(v_body_2277_, 0);
lean_inc_ref(v_expr_2304_);
v_type_x3f_2305_ = lean_ctor_get(v_body_2277_, 1);
lean_inc(v_type_x3f_2305_);
lean_dec_ref(v_body_2277_);
v___x_2306_ = lean_expr_abstract(v_expr_2304_, v_fvars_2276_);
lean_dec_ref(v_expr_2304_);
if (lean_obj_tag(v_type_x3f_2305_) == 0)
{
v___y_2286_ = v___y_2301_;
v___y_2287_ = v___y_2300_;
v___y_2288_ = v___y_2302_;
v___y_2289_ = v___x_2306_;
v___y_2290_ = v___y_2303_;
v___y_2291_ = v___y_2299_;
v___y_2292_ = v___y_2298_;
v___y_2293_ = v_type_x3f_2305_;
goto v___jp_2285_;
}
else
{
lean_object* v_val_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
v_val_2307_ = lean_ctor_get(v_type_x3f_2305_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_type_x3f_2305_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v_type_x3f_2305_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_val_2307_);
lean_dec(v_type_x3f_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_expr_abstract(v_val_2307_, v_fvars_2276_);
lean_dec(v_val_2307_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
v___y_2286_ = v___y_2301_;
v___y_2287_ = v___y_2300_;
v___y_2288_ = v___y_2302_;
v___y_2289_ = v___x_2306_;
v___y_2290_ = v___y_2303_;
v___y_2291_ = v___y_2299_;
v___y_2292_ = v___y_2298_;
v___y_2293_ = v___x_2313_;
goto v___jp_2285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2353_, lean_object* v_body_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2353_, v_body_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec(v_a_2355_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2363_, lean_object* v_n_2364_, lean_object* v_i_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2363_, v_i_2365_, v_a_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2376_, lean_object* v_n_2377_, lean_object* v_i_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2376_, v_n_2377_, v_i_2378_, v_a_2379_, v_a_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec(v_n_2377_);
lean_dec_ref(v_fvars_2376_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2389_, lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2389_, v_msg_2390_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2399_, lean_object* v_msg_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2399_, v_msg_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec(v___y_2401_);
return v_res_2408_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2414_ = l_Lean_stringToMessageData(v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2415_, lean_object* v_structName_2416_, lean_object* v_idx_2417_, lean_object* v_a_2418_, lean_object* v_00_u03b1_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_expr_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2443_; 
v_expr_2428_ = lean_ctor_get(v_struct_2415_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_struct_2415_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v_struct_2415_, 1);
lean_dec(v_unused_2444_);
v___x_2430_ = v_struct_2415_;
v_isShared_2431_ = v_isSharedCheck_2443_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_expr_2428_);
lean_dec(v_struct_2415_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2443_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2432_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2433_ = l_Lean_mkProj(v_structName_2416_, v_idx_2417_, v_expr_2428_);
v___x_2434_ = l_Lean_indentExpr(v___x_2433_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 7);
lean_ctor_set(v___x_2430_, 1, v___x_2434_);
lean_ctor_set(v___x_2430_, 0, v___x_2432_);
v___x_2436_ = v___x_2430_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2437_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = l_Lean_indentExpr(v_a_2418_);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2440_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2445_, lean_object* v_structName_2446_, lean_object* v_idx_2447_, lean_object* v_a_2448_, lean_object* v_00_u03b1_2449_, lean_object* v_x_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2445_, v_structName_2446_, v_idx_2447_, v_a_2448_, v_00_u03b1_2449_, v_x_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec(v___y_2451_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; lean_object* v_env_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2467_ = lean_st_ref_get(v___y_2465_);
v_env_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_env_2468_);
lean_dec(v___x_2467_);
v___x_2469_ = 0;
lean_inc(v_constName_2459_);
v___x_2470_ = l_Lean_Environment_find_x3f(v_env_2468_, v_constName_2459_, v___x_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v___x_2471_;
}
else
{
lean_object* v_val_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_constName_2459_);
v_val_2472_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2470_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_val_2472_);
lean_dec(v___x_2470_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 0);
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_val_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2489_, lean_object* v_structName_2490_, lean_object* v_idx_2491_, lean_object* v_a_2492_, lean_object* v_00_u03b1_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_expr_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2517_; 
v_expr_2502_ = lean_ctor_get(v_struct_2489_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_struct_2489_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v_struct_2489_, 1);
lean_dec(v_unused_2518_);
v___x_2504_ = v_struct_2489_;
v_isShared_2505_ = v_isSharedCheck_2517_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_expr_2502_);
lean_dec(v_struct_2489_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2517_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2506_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2507_ = l_Lean_mkProj(v_structName_2490_, v_idx_2491_, v_expr_2502_);
v___x_2508_ = l_Lean_indentExpr(v___x_2507_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 7);
lean_ctor_set(v___x_2504_, 1, v___x_2508_);
lean_ctor_set(v___x_2504_, 0, v___x_2506_);
v___x_2510_ = v___x_2504_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2511_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = l_Lean_indentExpr(v_a_2492_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2514_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2519_, lean_object* v_structName_2520_, lean_object* v_idx_2521_, lean_object* v_a_2522_, lean_object* v_00_u03b1_2523_, lean_object* v_x_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2519_, v_structName_2520_, v_idx_2521_, v_a_2522_, v_00_u03b1_2523_, v_x_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec(v___y_2525_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2533_, lean_object* v_fst_2534_, lean_object* v_struct_2535_, lean_object* v_structName_2536_, uint8_t v_a_2537_, lean_object* v___f_2538_, lean_object* v_snd_2539_, lean_object* v_____r_2540_, lean_object* v_ctorType_2541_, lean_object* v_j_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
if (lean_obj_tag(v_ctorType_2541_) == 7)
{
lean_object* v_binderType_2550_; lean_object* v_body_2551_; lean_object* v___x_2552_; 
lean_dec(v_snd_2539_);
v_binderType_2550_ = lean_ctor_get(v_ctorType_2541_, 1);
lean_inc_ref(v_binderType_2550_);
v_body_2551_ = lean_ctor_get(v_ctorType_2541_, 2);
lean_inc_ref(v_body_2551_);
lean_dec_ref_known(v_ctorType_2541_, 3);
v___x_2552_ = lean_expr_instantiate_rev_range(v_binderType_2550_, v_j_2542_, v_a_2533_, v_fst_2534_);
lean_dec_ref(v_binderType_2550_);
if (v_a_2537_ == 0)
{
lean_dec_ref(v___f_2538_);
goto v___jp_2553_;
}
else
{
lean_object* v___x_2569_; 
lean_inc_ref(v___x_2552_);
v___x_2569_ = l_Lean_Meta_isProp(v___x_2552_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; uint8_t v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = lean_unbox(v_a_2570_);
lean_dec(v_a_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_box(0);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
lean_inc(v___y_2544_);
lean_inc(v___y_2543_);
v___x_2573_ = lean_apply_9(v___f_2538_, lean_box(0), v___x_2572_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, lean_box(0));
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_dec_ref_known(v___x_2573_, 1);
goto v___jp_2553_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v___x_2552_);
lean_dec_ref(v_body_2551_);
lean_dec(v_structName_2536_);
lean_dec_ref(v_struct_2535_);
lean_dec(v_fst_2534_);
lean_dec(v_a_2533_);
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_dec_ref(v___f_2538_);
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec_ref(v___x_2552_);
lean_dec_ref(v_body_2551_);
lean_dec_ref(v___f_2538_);
lean_dec(v_structName_2536_);
lean_dec_ref(v_struct_2535_);
lean_dec(v_fst_2534_);
lean_dec(v_a_2533_);
v_a_2582_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2569_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2569_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
v___jp_2553_:
{
lean_object* v_expr_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2567_; 
v_expr_2554_ = lean_ctor_get(v_struct_2535_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_struct_2535_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v_struct_2535_, 1);
lean_dec(v_unused_2568_);
v___x_2556_ = v_struct_2535_;
v_isShared_2557_ = v_isSharedCheck_2567_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_expr_2554_);
lean_dec(v_struct_2535_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2567_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2558_ = l_Lean_Expr_proj___override(v_structName_2536_, v_a_2533_, v_expr_2554_);
v___x_2559_ = lean_array_push(v_fst_2534_, v___x_2558_);
lean_inc(v_j_2542_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v___x_2552_);
lean_ctor_set(v___x_2556_, 0, v_j_2542_);
v___x_2561_ = v___x_2556_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_j_2542_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v___x_2552_);
v___x_2561_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2559_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_body_2551_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
}
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v_structName_2536_);
lean_dec_ref(v_struct_2535_);
lean_dec(v_a_2533_);
v___x_2590_ = lean_box(0);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
lean_inc(v___y_2544_);
lean_inc(v___y_2543_);
v___x_2591_ = lean_apply_9(v___f_2538_, lean_box(0), v___x_2590_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, lean_box(0));
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2602_; 
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v___x_2591_, 0);
lean_dec(v_unused_2603_);
v___x_2593_ = v___x_2591_;
v_isShared_2594_ = v_isSharedCheck_2602_;
goto v_resetjp_2592_;
}
else
{
lean_dec(v___x_2591_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2602_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_inc(v_j_2542_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_j_2542_);
lean_ctor_set(v___x_2595_, 1, v_snd_2539_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_fst_2534_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v_ctorType_2541_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2598_);
v___x_2600_ = v___x_2593_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_ctorType_2541_);
lean_dec(v_snd_2539_);
lean_dec(v_fst_2534_);
v_a_2604_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2591_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2591_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2612_ = _args[0];
lean_object* v_fst_2613_ = _args[1];
lean_object* v_struct_2614_ = _args[2];
lean_object* v_structName_2615_ = _args[3];
lean_object* v_a_2616_ = _args[4];
lean_object* v___f_2617_ = _args[5];
lean_object* v_snd_2618_ = _args[6];
lean_object* v_____r_2619_ = _args[7];
lean_object* v_ctorType_2620_ = _args[8];
lean_object* v_j_2621_ = _args[9];
lean_object* v___y_2622_ = _args[10];
lean_object* v___y_2623_ = _args[11];
lean_object* v___y_2624_ = _args[12];
lean_object* v___y_2625_ = _args[13];
lean_object* v___y_2626_ = _args[14];
lean_object* v___y_2627_ = _args[15];
lean_object* v___y_2628_ = _args[16];
_start:
{
uint8_t v_a_19035__boxed_2629_; lean_object* v_res_2630_; 
v_a_19035__boxed_2629_ = lean_unbox(v_a_2616_);
v_res_2630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2612_, v_fst_2613_, v_struct_2614_, v_structName_2615_, v_a_19035__boxed_2629_, v___f_2617_, v_snd_2618_, v_____r_2619_, v_ctorType_2620_, v_j_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec(v_j_2621_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2631_, lean_object* v_struct_2632_, lean_object* v_structName_2633_, uint8_t v_a_2634_, lean_object* v_idx_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___y_2647_; uint8_t v___x_2669_; 
v___x_2669_ = lean_nat_dec_le(v_a_2637_, v_upperBound_2631_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_idx_2635_);
lean_dec(v_structName_2633_);
lean_dec_ref(v_struct_2632_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_b_2638_);
return v___x_2670_;
}
else
{
lean_object* v_snd_2671_; lean_object* v_snd_2672_; lean_object* v_fst_2673_; lean_object* v_fst_2674_; lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v___f_2677_; uint8_t v___x_2678_; 
v_snd_2671_ = lean_ctor_get(v_b_2638_, 1);
lean_inc(v_snd_2671_);
v_snd_2672_ = lean_ctor_get(v_snd_2671_, 1);
lean_inc(v_snd_2672_);
v_fst_2673_ = lean_ctor_get(v_b_2638_, 0);
lean_inc(v_fst_2673_);
lean_dec_ref(v_b_2638_);
v_fst_2674_ = lean_ctor_get(v_snd_2671_, 0);
lean_inc(v_fst_2674_);
lean_dec(v_snd_2671_);
v_fst_2675_ = lean_ctor_get(v_snd_2672_, 0);
lean_inc(v_fst_2675_);
v_snd_2676_ = lean_ctor_get(v_snd_2672_, 1);
lean_inc(v_snd_2676_);
lean_dec(v_snd_2672_);
lean_inc_ref(v_a_2636_);
lean_inc(v_idx_2635_);
lean_inc(v_structName_2633_);
lean_inc_ref(v_struct_2632_);
v___f_2677_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2677_, 0, v_struct_2632_);
lean_closure_set(v___f_2677_, 1, v_structName_2633_);
lean_closure_set(v___f_2677_, 2, v_idx_2635_);
lean_closure_set(v___f_2677_, 3, v_a_2636_);
v___x_2678_ = l_Lean_Expr_isForall(v_fst_2673_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_expr_instantiate_rev_range(v_fst_2673_, v_fst_2675_, v_a_2637_, v_fst_2674_);
lean_dec(v_fst_2675_);
lean_dec(v_fst_2673_);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
v___x_2680_ = lean_whnf(v___x_2679_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = lean_box(0);
lean_inc(v_structName_2633_);
lean_inc_ref(v_struct_2632_);
lean_inc(v_a_2637_);
v___x_2683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2637_, v_fst_2674_, v_struct_2632_, v_structName_2633_, v_a_2634_, v___f_2677_, v_snd_2676_, v___x_2682_, v_a_2681_, v_a_2637_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
v___y_2647_ = v___x_2683_;
goto v___jp_2646_;
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v___f_2677_);
lean_dec(v_snd_2676_);
lean_dec(v_fst_2674_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_idx_2635_);
lean_dec(v_structName_2633_);
lean_dec_ref(v_struct_2632_);
v_a_2684_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2680_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2680_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_box(0);
lean_inc(v_structName_2633_);
lean_inc_ref(v_struct_2632_);
lean_inc(v_a_2637_);
v___x_2693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2637_, v_fst_2674_, v_struct_2632_, v_structName_2633_, v_a_2634_, v___f_2677_, v_snd_2676_, v___x_2692_, v_fst_2673_, v_fst_2675_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v_fst_2675_);
v___y_2647_ = v___x_2693_;
goto v___jp_2646_;
}
}
v___jp_2646_:
{
if (lean_obj_tag(v___y_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2660_; 
v_a_2648_ = lean_ctor_get(v___y_2647_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___y_2647_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2650_ = v___y_2647_;
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___y_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
if (lean_obj_tag(v_a_2648_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; 
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_idx_2635_);
lean_dec(v_structName_2633_);
lean_dec_ref(v_struct_2632_);
v_a_2652_ = lean_ctor_get(v_a_2648_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v_a_2648_, 1);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v_a_2652_);
v___x_2654_ = v___x_2650_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_del_object(v___x_2650_);
v_a_2656_ = lean_ctor_get(v_a_2648_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v_a_2648_, 1);
v___x_2657_ = lean_unsigned_to_nat(1u);
v___x_2658_ = lean_nat_add(v_a_2637_, v___x_2657_);
lean_dec(v_a_2637_);
v_a_2637_ = v___x_2658_;
v_b_2638_ = v_a_2656_;
goto _start;
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_idx_2635_);
lean_dec(v_structName_2633_);
lean_dec_ref(v_struct_2632_);
v_a_2661_ = lean_ctor_get(v___y_2647_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___y_2647_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___y_2647_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___y_2647_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2694_, lean_object* v_struct_2695_, lean_object* v_structName_2696_, lean_object* v_a_2697_, lean_object* v_idx_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_b_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
uint8_t v_a_19192__boxed_2709_; lean_object* v_res_2710_; 
v_a_19192__boxed_2709_ = lean_unbox(v_a_2697_);
v_res_2710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2694_, v_struct_2695_, v_structName_2696_, v_a_19192__boxed_2709_, v_idx_2698_, v_a_2699_, v_a_2700_, v_b_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec(v_upperBound_2694_);
return v_res_2710_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2714_ = lean_unsigned_to_nat(18u);
v___x_2715_ = lean_unsigned_to_nat(1913u);
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2717_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2718_ = l_mkPanicMessageWithDecl(v___x_2717_, v___x_2716_, v___x_2715_, v___x_2714_, v___x_2713_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v___x_2719_);
return v___x_2721_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2723_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v___x_2722_);
return v___x_2724_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2725_; lean_object* v_dummy_2726_; 
v___x_2725_ = lean_box(0);
v_dummy_2726_ = l_Lean_Expr_sort___override(v___x_2725_);
return v_dummy_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2727_, lean_object* v_structName_2728_, lean_object* v_idx_2729_, lean_object* v_struct_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2745_; uint8_t v___x_2749_; 
v___x_2749_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2731_);
if (v___x_2749_ == 0)
{
lean_dec(v_idx_2729_);
lean_dec(v_structName_2728_);
if (lean_obj_tag(v_e_2727_) == 11)
{
lean_object* v_expr_2750_; lean_object* v_typeName_2751_; lean_object* v_idx_2752_; lean_object* v_struct_2753_; size_t v___x_2754_; size_t v___x_2755_; uint8_t v___x_2756_; 
v_expr_2750_ = lean_ctor_get(v_struct_2730_, 0);
lean_inc_ref(v_expr_2750_);
lean_dec_ref(v_struct_2730_);
v_typeName_2751_ = lean_ctor_get(v_e_2727_, 0);
v_idx_2752_ = lean_ctor_get(v_e_2727_, 1);
v_struct_2753_ = lean_ctor_get(v_e_2727_, 2);
v___x_2754_ = lean_ptr_addr(v_struct_2753_);
v___x_2755_ = lean_ptr_addr(v_expr_2750_);
v___x_2756_ = lean_usize_dec_eq(v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; 
lean_inc(v_idx_2752_);
lean_inc(v_typeName_2751_);
lean_dec_ref_known(v_e_2727_, 3);
v___x_2757_ = l_Lean_Expr_proj___override(v_typeName_2751_, v_idx_2752_, v_expr_2750_);
v___y_2745_ = v___x_2757_;
goto v___jp_2744_;
}
else
{
lean_dec_ref(v_expr_2750_);
v___y_2745_ = v_e_2727_;
goto v___jp_2744_;
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec_ref(v_struct_2730_);
lean_dec_ref(v_e_2727_);
v___x_2758_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2759_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2758_);
v___y_2745_ = v___x_2759_;
goto v___jp_2744_;
}
}
else
{
lean_object* v___x_2760_; 
lean_inc_ref(v_struct_2730_);
v___x_2760_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2730_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
lean_inc(v_a_2736_);
lean_inc_ref(v_a_2735_);
lean_inc(v_a_2734_);
lean_inc_ref(v_a_2733_);
v___x_2762_ = lean_whnf(v_a_2761_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc_n(v_a_2763_, 2);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = l_Lean_Meta_isProp(v_a_2763_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l_Lean_Expr_getAppFn(v_a_2763_);
if (lean_obj_tag(v___x_2766_) == 4)
{
lean_object* v_declName_2767_; lean_object* v_us_2768_; lean_object* v___x_2769_; lean_object* v_env_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; 
v_declName_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_declName_2767_);
v_us_2768_ = lean_ctor_get(v___x_2766_, 1);
lean_inc(v_us_2768_);
lean_dec_ref_known(v___x_2766_, 2);
v___x_2769_ = lean_st_ref_get(v_a_2736_);
v_env_2773_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_ref(v_env_2773_);
lean_dec(v___x_2769_);
v___x_2774_ = 0;
v___x_2775_ = l_Lean_Environment_find_x3f(v_env_2773_, v_declName_2767_, v___x_2774_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
v___x_2776_ = lean_box(0);
v___x_2777_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2730_, v_structName_2728_, v_idx_2729_, v_a_2763_, lean_box(0), v___x_2776_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
return v___x_2777_;
}
else
{
lean_object* v_val_2778_; 
v_val_2778_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_val_2778_);
lean_dec_ref_known(v___x_2775_, 1);
if (lean_obj_tag(v_val_2778_) == 5)
{
lean_object* v_val_2779_; lean_object* v_ctors_2780_; 
v_val_2779_ = lean_ctor_get(v_val_2778_, 0);
lean_inc_ref(v_val_2779_);
lean_dec_ref_known(v_val_2778_, 1);
v_ctors_2780_ = lean_ctor_get(v_val_2779_, 4);
lean_inc(v_ctors_2780_);
if (lean_obj_tag(v_ctors_2780_) == 1)
{
lean_object* v_tail_2781_; 
v_tail_2781_ = lean_ctor_get(v_ctors_2780_, 1);
if (lean_obj_tag(v_tail_2781_) == 0)
{
lean_object* v_toConstantVal_2782_; lean_object* v_numParams_2783_; lean_object* v_numIndices_2784_; lean_object* v_head_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2894_; 
v_toConstantVal_2782_ = lean_ctor_get(v_val_2779_, 0);
lean_inc_ref(v_toConstantVal_2782_);
v_numParams_2783_ = lean_ctor_get(v_val_2779_, 1);
lean_inc(v_numParams_2783_);
v_numIndices_2784_ = lean_ctor_get(v_val_2779_, 2);
lean_inc(v_numIndices_2784_);
lean_dec_ref(v_val_2779_);
v_head_2785_ = lean_ctor_get(v_ctors_2780_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_ctors_2780_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v_ctors_2780_, 1);
lean_dec(v_unused_2895_);
v___x_2787_ = v_ctors_2780_;
v_isShared_2788_ = v_isSharedCheck_2894_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_head_2785_);
lean_dec(v_ctors_2780_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2894_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2785_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
if (lean_obj_tag(v_a_2790_) == 6)
{
lean_object* v_val_2791_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v_name_2872_; uint8_t v___x_2873_; 
v_val_2791_ = lean_ctor_get(v_a_2790_, 0);
lean_inc_ref(v_val_2791_);
lean_dec_ref_known(v_a_2790_, 1);
v_name_2872_ = lean_ctor_get(v_toConstantVal_2782_, 0);
lean_inc(v_name_2872_);
lean_dec_ref(v_toConstantVal_2782_);
v___x_2873_ = lean_name_eq(v_name_2872_, v_structName_2728_);
lean_dec(v_name_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v_val_2791_);
lean_del_object(v___x_2787_);
lean_dec(v_numIndices_2784_);
lean_dec(v_numParams_2783_);
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
v___x_2874_ = lean_box(0);
v___x_2875_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2730_, v_structName_2728_, v_idx_2729_, v_a_2763_, lean_box(0), v___x_2874_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
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
else
{
v___y_2847_ = v_a_2731_;
v___y_2848_ = v_a_2732_;
v___y_2849_ = v_a_2733_;
v___y_2850_ = v_a_2734_;
v___y_2851_ = v_a_2735_;
v___y_2852_ = v_a_2736_;
goto v___jp_2846_;
}
v___jp_2792_:
{
lean_object* v_toConstantVal_2800_; lean_object* v_name_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_toConstantVal_2800_ = lean_ctor_get(v_val_2791_, 0);
lean_inc_ref(v_toConstantVal_2800_);
lean_dec_ref(v_val_2791_);
v_name_2801_ = lean_ctor_get(v_toConstantVal_2800_, 0);
lean_inc(v_name_2801_);
lean_dec_ref(v_toConstantVal_2800_);
v___x_2802_ = l_Lean_mkConst(v_name_2801_, v_us_2768_);
v___x_2803_ = lean_unsigned_to_nat(0u);
v___x_2804_ = l_Array_toSubarray___redArg(v___y_2793_, v___x_2803_, v_numParams_2783_);
v___x_2805_ = l_Subarray_copy___redArg(v___x_2804_);
v___x_2806_ = l_Lean_mkAppN(v___x_2802_, v___x_2805_);
lean_dec_ref(v___x_2805_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
v___x_2807_ = lean_infer_type(v___x_2806_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 0);
lean_ctor_set(v___x_2787_, 1, v___x_2809_);
lean_ctor_set(v___x_2787_, 0, v_a_2808_);
v___x_2811_ = v___x_2787_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2808_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
uint8_t v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = lean_unbox(v_a_2765_);
lean_dec(v_a_2765_);
lean_inc_ref(v_struct_2730_);
lean_inc(v_idx_2729_);
v___x_2813_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2729_, v_struct_2730_, v_structName_2728_, v___x_2812_, v_idx_2729_, v_a_2763_, v___x_2803_, v___x_2811_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v_idx_2729_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v_snd_2815_; lean_object* v_snd_2816_; lean_object* v_snd_2817_; lean_object* v_expr_2818_; lean_object* v___x_2819_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v_snd_2815_ = lean_ctor_get(v_a_2814_, 1);
lean_inc(v_snd_2815_);
lean_dec(v_a_2814_);
v_snd_2816_ = lean_ctor_get(v_snd_2815_, 1);
lean_inc(v_snd_2816_);
lean_dec(v_snd_2815_);
v_snd_2817_ = lean_ctor_get(v_snd_2816_, 1);
lean_inc(v_snd_2817_);
lean_dec(v_snd_2816_);
v_expr_2818_ = lean_ctor_get(v_struct_2730_, 0);
lean_inc_ref(v_expr_2818_);
lean_dec_ref(v_struct_2730_);
v___x_2819_ = l_Lean_Expr_cleanupAnnotations(v_snd_2817_);
if (lean_obj_tag(v_e_2727_) == 11)
{
lean_object* v_typeName_2820_; lean_object* v_idx_2821_; lean_object* v_struct_2822_; size_t v___x_2823_; size_t v___x_2824_; uint8_t v___x_2825_; 
v_typeName_2820_ = lean_ctor_get(v_e_2727_, 0);
v_idx_2821_ = lean_ctor_get(v_e_2727_, 1);
v_struct_2822_ = lean_ctor_get(v_e_2727_, 2);
v___x_2823_ = lean_ptr_addr(v_struct_2822_);
v___x_2824_ = lean_ptr_addr(v_expr_2818_);
v___x_2825_ = lean_usize_dec_eq(v___x_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
lean_inc(v_idx_2821_);
lean_inc(v_typeName_2820_);
lean_dec_ref_known(v_e_2727_, 3);
v___x_2826_ = l_Lean_Expr_proj___override(v_typeName_2820_, v_idx_2821_, v_expr_2818_);
v___y_2739_ = v___x_2819_;
v___y_2740_ = v___x_2826_;
goto v___jp_2738_;
}
else
{
lean_dec_ref(v_expr_2818_);
v___y_2739_ = v___x_2819_;
v___y_2740_ = v_e_2727_;
goto v___jp_2738_;
}
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v_expr_2818_);
lean_dec_ref(v_e_2727_);
v___x_2827_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2828_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2827_);
v___y_2739_ = v___x_2819_;
v___y_2740_ = v___x_2828_;
goto v___jp_2738_;
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v_struct_2730_);
lean_dec_ref(v_e_2727_);
v_a_2829_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2813_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2813_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_del_object(v___x_2787_);
lean_dec(v_a_2765_);
lean_dec(v_a_2763_);
lean_dec_ref(v_struct_2730_);
lean_dec(v_idx_2729_);
lean_dec(v_structName_2728_);
lean_dec_ref(v_e_2727_);
v_a_2838_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2807_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2807_);
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
v___jp_2846_:
{
lean_object* v_dummy_2853_; lean_object* v_nargs_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_dummy_2853_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2854_ = l_Lean_Expr_getAppNumArgs(v_a_2763_);
lean_inc(v_nargs_2854_);
v___x_2855_ = lean_mk_array(v_nargs_2854_, v_dummy_2853_);
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = lean_nat_sub(v_nargs_2854_, v___x_2856_);
lean_dec(v_nargs_2854_);
lean_inc(v_a_2763_);
v___x_2858_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2763_, v___x_2855_, v___x_2857_);
v___x_2859_ = lean_nat_add(v_numParams_2783_, v_numIndices_2784_);
lean_dec(v_numIndices_2784_);
v___x_2860_ = lean_array_get_size(v___x_2858_);
v___x_2861_ = lean_nat_dec_eq(v___x_2859_, v___x_2860_);
lean_dec(v___x_2859_);
if (v___x_2861_ == 0)
{
if (v___x_2749_ == 0)
{
v___y_2793_ = v___x_2858_;
v___y_2794_ = v___y_2847_;
v___y_2795_ = v___y_2848_;
v___y_2796_ = v___y_2849_;
v___y_2797_ = v___y_2850_;
v___y_2798_ = v___y_2851_;
v___y_2799_ = v___y_2852_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v___x_2858_);
lean_dec_ref(v_val_2791_);
lean_del_object(v___x_2787_);
lean_dec(v_numParams_2783_);
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
v___x_2862_ = lean_box(0);
v___x_2863_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2730_, v_structName_2728_, v_idx_2729_, v_a_2763_, lean_box(0), v___x_2862_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
v___y_2793_ = v___x_2858_;
v___y_2794_ = v___y_2847_;
v___y_2795_ = v___y_2848_;
v___y_2796_ = v___y_2849_;
v___y_2797_ = v___y_2850_;
v___y_2798_ = v___y_2851_;
v___y_2799_ = v___y_2852_;
goto v___jp_2792_;
}
}
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_dec(v_a_2790_);
lean_del_object(v___x_2787_);
lean_dec(v_numIndices_2784_);
lean_dec(v_numParams_2783_);
lean_dec_ref(v_toConstantVal_2782_);
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
v___x_2884_ = lean_box(0);
v___x_2885_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2730_, v_structName_2728_, v_idx_2729_, v_a_2763_, lean_box(0), v___x_2884_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
return v___x_2885_;
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_del_object(v___x_2787_);
lean_dec(v_numIndices_2784_);
lean_dec(v_numParams_2783_);
lean_dec_ref(v_toConstantVal_2782_);
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec(v_a_2763_);
lean_dec_ref(v_struct_2730_);
lean_dec(v_idx_2729_);
lean_dec(v_structName_2728_);
lean_dec_ref(v_e_2727_);
v_a_2886_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2789_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2789_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2780_, 2);
lean_dec_ref(v_val_2779_);
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
goto v___jp_2770_;
}
}
else
{
lean_dec(v_ctors_2780_);
lean_dec_ref(v_val_2779_);
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
goto v___jp_2770_;
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_dec(v_val_2778_);
lean_dec(v_us_2768_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
v___x_2896_ = lean_box(0);
v___x_2897_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2730_, v_structName_2728_, v_idx_2729_, v_a_2763_, lean_box(0), v___x_2896_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
return v___x_2897_;
}
}
v___jp_2770_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_box(0);
v___x_2772_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2730_, v_structName_2728_, v_idx_2729_, v_a_2763_, lean_box(0), v___x_2771_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
return v___x_2772_;
}
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec_ref(v___x_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2727_);
v___x_2898_ = lean_box(0);
v___x_2899_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2730_, v_structName_2728_, v_idx_2729_, v_a_2763_, lean_box(0), v___x_2898_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
return v___x_2899_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_a_2763_);
lean_dec_ref(v_struct_2730_);
lean_dec(v_idx_2729_);
lean_dec(v_structName_2728_);
lean_dec_ref(v_e_2727_);
v_a_2900_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2764_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2764_);
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
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v_struct_2730_);
lean_dec(v_idx_2729_);
lean_dec(v_structName_2728_);
lean_dec_ref(v_e_2727_);
v_a_2908_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2762_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2762_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v_struct_2730_);
lean_dec(v_idx_2729_);
lean_dec(v_structName_2728_);
lean_dec_ref(v_e_2727_);
v_a_2916_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2760_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2760_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
v___jp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___y_2739_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___y_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
return v___x_2743_;
}
v___jp_2744_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___y_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2924_, lean_object* v_structName_2925_, lean_object* v_idx_2926_, lean_object* v_struct_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2924_, v_structName_2925_, v_idx_2926_, v_struct_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec(v_a_2928_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2936_, lean_object* v_struct_2937_, lean_object* v_structName_2938_, uint8_t v_a_2939_, lean_object* v_idx_2940_, lean_object* v_a_2941_, lean_object* v_inst_2942_, lean_object* v_R_2943_, lean_object* v_a_2944_, lean_object* v_b_2945_, lean_object* v_c_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2936_, v_struct_2937_, v_structName_2938_, v_a_2939_, v_idx_2940_, v_a_2941_, v_a_2944_, v_b_2945_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2955_ = _args[0];
lean_object* v_struct_2956_ = _args[1];
lean_object* v_structName_2957_ = _args[2];
lean_object* v_a_2958_ = _args[3];
lean_object* v_idx_2959_ = _args[4];
lean_object* v_a_2960_ = _args[5];
lean_object* v_inst_2961_ = _args[6];
lean_object* v_R_2962_ = _args[7];
lean_object* v_a_2963_ = _args[8];
lean_object* v_b_2964_ = _args[9];
lean_object* v_c_2965_ = _args[10];
lean_object* v___y_2966_ = _args[11];
lean_object* v___y_2967_ = _args[12];
lean_object* v___y_2968_ = _args[13];
lean_object* v___y_2969_ = _args[14];
lean_object* v___y_2970_ = _args[15];
lean_object* v___y_2971_ = _args[16];
lean_object* v___y_2972_ = _args[17];
_start:
{
uint8_t v_a_19716__boxed_2973_; lean_object* v_res_2974_; 
v_a_19716__boxed_2973_ = lean_unbox(v_a_2958_);
v_res_2974_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2955_, v_struct_2956_, v_structName_2957_, v_a_19716__boxed_2973_, v_idx_2959_, v_a_2960_, v_inst_2961_, v_R_2962_, v_a_2963_, v_b_2964_, v_c_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec(v_upperBound_2955_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2975_, size_t v_i_2976_, size_t v_stop_2977_, lean_object* v_b_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_usize_dec_eq(v_i_2976_, v_stop_2977_);
if (v___x_2985_ == 0)
{
size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2986_ = ((size_t)1ULL);
v___x_2987_ = lean_usize_sub(v_i_2976_, v___x_2986_);
v___x_2988_ = lean_array_uget_borrowed(v_as_2975_, v___x_2987_);
lean_inc(v___x_2988_);
v___x_2989_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2988_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = l_Lean_Expr_sortLevel_x21(v_a_2990_);
lean_dec(v_a_2990_);
v___x_2992_ = l_Lean_mkLevelIMax_x27(v___x_2991_, v_b_2978_);
v_i_2976_ = v___x_2987_;
v_b_2978_ = v___x_2992_;
goto _start;
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_b_2978_);
v_a_2994_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2989_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2989_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_b_2978_);
return v___x_3002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_3003_, lean_object* v_i_3004_, lean_object* v_stop_3005_, lean_object* v_b_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
size_t v_i_boxed_3013_; size_t v_stop_boxed_3014_; lean_object* v_res_3015_; 
v_i_boxed_3013_ = lean_unbox_usize(v_i_3004_);
lean_dec(v_i_3004_);
v_stop_boxed_3014_ = lean_unbox_usize(v_stop_3005_);
lean_dec(v_stop_3005_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3003_, v_i_boxed_3013_, v_stop_boxed_3014_, v_b_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v_as_3003_);
return v_res_3015_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_3020_ = lean_unsigned_to_nat(14u);
v___x_3021_ = lean_unsigned_to_nat(22u);
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_3024_ = l_mkPanicMessageWithDecl(v___x_3023_, v___x_3022_, v___x_3021_, v___x_3020_, v___x_3019_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_3025_, lean_object* v_doms_3026_, lean_object* v_body_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_lctx_3035_; lean_object* v_expr_3036_; uint8_t v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v_a_3041_; uint8_t v___x_3046_; 
v_lctx_3035_ = lean_ctor_get(v_a_3030_, 2);
v_expr_3036_ = lean_ctor_get(v_body_3027_, 0);
v___x_3037_ = 1;
v___x_3038_ = 0;
lean_inc_ref(v_lctx_3035_);
v___x_3039_ = l_Lean_LocalContext_mkForall(v_lctx_3035_, v_fvars_3025_, v_expr_3036_, v___x_3037_, v___x_3038_);
v___x_3046_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3028_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3055_; 
v_isSharedCheck_3055_ = !lean_is_exclusive(v_body_3027_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; lean_object* v_unused_3057_; 
v_unused_3056_ = lean_ctor_get(v_body_3027_, 1);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v_body_3027_, 0);
lean_dec(v_unused_3057_);
v___x_3048_ = v_body_3027_;
v_isShared_3049_ = v_isSharedCheck_3055_;
goto v_resetjp_3047_;
}
else
{
lean_dec(v_body_3027_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3055_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3050_ = lean_box(0);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v___x_3050_);
lean_ctor_set(v___x_3048_, 0, v___x_3039_);
v___x_3052_ = v___x_3048_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
}
}
else
{
lean_object* v___x_3058_; 
v___x_3058_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___y_3061_; lean_object* v_type_x3f_3078_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v_type_x3f_3078_ = lean_ctor_get(v_a_3059_, 1);
lean_inc(v_type_x3f_3078_);
lean_dec(v_a_3059_);
if (lean_obj_tag(v_type_x3f_3078_) == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3080_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3079_);
v___y_3061_ = v___x_3080_;
goto v___jp_3060_;
}
else
{
lean_object* v_val_3081_; 
v_val_3081_ = lean_ctor_get(v_type_x3f_3078_, 0);
lean_inc(v_val_3081_);
lean_dec_ref_known(v_type_x3f_3078_, 1);
v___y_3061_ = v_val_3081_;
goto v___jp_3060_;
}
v___jp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3062_ = l_Lean_Expr_sortLevel_x21(v___y_3061_);
lean_dec_ref(v___y_3061_);
v___x_3063_ = lean_array_get_size(v_doms_3026_);
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = lean_nat_dec_lt(v___x_3064_, v___x_3063_);
if (v___x_3065_ == 0)
{
v_a_3041_ = v___x_3062_;
goto v___jp_3040_;
}
else
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_usize_of_nat(v___x_3063_);
v___x_3067_ = ((size_t)0ULL);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_3026_, v___x_3066_, v___x_3067_, v___x_3062_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v_a_3041_ = v_a_3069_;
goto v___jp_3040_;
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v___x_3039_);
v_a_3070_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3068_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3068_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3039_);
return v___x_3058_;
}
}
v___jp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3042_ = l_Lean_Expr_sort___override(v_a_3041_);
v___x_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3039_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3082_, lean_object* v_doms_3083_, lean_object* v_body_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3082_, v_doms_3083_, v_body_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_doms_3083_);
lean_dec_ref(v_fvars_3082_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3093_, size_t v_i_3094_, size_t v_stop_3095_, lean_object* v_b_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3093_, v_i_3094_, v_stop_3095_, v_b_3096_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3105_, lean_object* v_i_3106_, lean_object* v_stop_3107_, lean_object* v_b_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
size_t v_i_boxed_3116_; size_t v_stop_boxed_3117_; lean_object* v_res_3118_; 
v_i_boxed_3116_ = lean_unbox_usize(v_i_3106_);
lean_dec(v_i_3106_);
v_stop_boxed_3117_ = lean_unbox_usize(v_stop_3107_);
lean_dec(v_stop_3107_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3105_, v_i_boxed_3116_, v_stop_boxed_3117_, v_b_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v_as_3105_);
return v_res_3118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3119_, lean_object* v_opt_3120_){
_start:
{
lean_object* v_name_3121_; lean_object* v_defValue_3122_; lean_object* v_map_3123_; lean_object* v___x_3124_; 
v_name_3121_ = lean_ctor_get(v_opt_3120_, 0);
v_defValue_3122_ = lean_ctor_get(v_opt_3120_, 1);
v_map_3123_ = lean_ctor_get(v_opts_3119_, 0);
v___x_3124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3123_, v_name_3121_);
if (lean_obj_tag(v___x_3124_) == 0)
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_unbox(v_defValue_3122_);
return v___x_3125_;
}
else
{
lean_object* v_val_3126_; 
v_val_3126_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3124_, 1);
if (lean_obj_tag(v_val_3126_) == 1)
{
uint8_t v_v_3127_; 
v_v_3127_ = lean_ctor_get_uint8(v_val_3126_, 0);
lean_dec_ref_known(v_val_3126_, 0);
return v_v_3127_;
}
else
{
uint8_t v___x_3128_; 
lean_dec(v_val_3126_);
v___x_3128_ = lean_unbox(v_defValue_3122_);
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3129_, lean_object* v_opt_3130_){
_start:
{
uint8_t v_res_3131_; lean_object* v_r_3132_; 
v_res_3131_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3129_, v_opt_3130_);
lean_dec_ref(v_opt_3130_);
lean_dec_ref(v_opts_3129_);
v_r_3132_ = lean_box(v_res_3131_);
return v_r_3132_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3133_){
_start:
{
if (lean_obj_tag(v_x_3133_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
v_a_3135_ = lean_ctor_get(v_x_3133_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_x_3133_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v_x_3133_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v_x_3133_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set_tag(v___x_3137_, 1);
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_a_3143_ = lean_ctor_get(v_x_3133_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_x_3133_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v_x_3133_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v_x_3133_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 0);
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3151_);
return v_res_3153_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3154_){
_start:
{
if (lean_obj_tag(v_e_3154_) == 0)
{
uint8_t v___x_3155_; 
v___x_3155_ = 2;
return v___x_3155_;
}
else
{
uint8_t v___x_3156_; 
v___x_3156_ = 0;
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3157_);
lean_dec_ref(v_e_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3160_, lean_object* v_opt_3161_){
_start:
{
lean_object* v_name_3162_; lean_object* v_defValue_3163_; lean_object* v_map_3164_; lean_object* v___x_3165_; 
v_name_3162_ = lean_ctor_get(v_opt_3161_, 0);
v_defValue_3163_ = lean_ctor_get(v_opt_3161_, 1);
v_map_3164_ = lean_ctor_get(v_opts_3160_, 0);
v___x_3165_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3164_, v_name_3162_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_inc(v_defValue_3163_);
return v_defValue_3163_;
}
else
{
lean_object* v_val_3166_; 
v_val_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_val_3166_);
lean_dec_ref_known(v___x_3165_, 1);
if (lean_obj_tag(v_val_3166_) == 3)
{
lean_object* v_v_3167_; 
v_v_3167_ = lean_ctor_get(v_val_3166_, 0);
lean_inc(v_v_3167_);
lean_dec_ref_known(v_val_3166_, 1);
return v_v_3167_;
}
else
{
lean_dec(v_val_3166_);
lean_inc(v_defValue_3163_);
return v_defValue_3163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3168_, lean_object* v_opt_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3168_, v_opt_3169_);
lean_dec_ref(v_opt_3169_);
lean_dec_ref(v_opts_3168_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3171_, size_t v_i_3172_, lean_object* v_bs_3173_){
_start:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_usize_dec_lt(v_i_3172_, v_sz_3171_);
if (v___x_3174_ == 0)
{
return v_bs_3173_;
}
else
{
lean_object* v_v_3175_; lean_object* v_msg_3176_; lean_object* v___x_3177_; lean_object* v_bs_x27_3178_; size_t v___x_3179_; size_t v___x_3180_; lean_object* v___x_3181_; 
v_v_3175_ = lean_array_uget_borrowed(v_bs_3173_, v_i_3172_);
v_msg_3176_ = lean_ctor_get(v_v_3175_, 1);
lean_inc_ref(v_msg_3176_);
v___x_3177_ = lean_unsigned_to_nat(0u);
v_bs_x27_3178_ = lean_array_uset(v_bs_3173_, v_i_3172_, v___x_3177_);
v___x_3179_ = ((size_t)1ULL);
v___x_3180_ = lean_usize_add(v_i_3172_, v___x_3179_);
v___x_3181_ = lean_array_uset(v_bs_x27_3178_, v_i_3172_, v_msg_3176_);
v_i_3172_ = v___x_3180_;
v_bs_3173_ = v___x_3181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3183_, lean_object* v_i_3184_, lean_object* v_bs_3185_){
_start:
{
size_t v_sz_boxed_3186_; size_t v_i_boxed_3187_; lean_object* v_res_3188_; 
v_sz_boxed_3186_ = lean_unbox_usize(v_sz_3183_);
lean_dec(v_sz_3183_);
v_i_boxed_3187_ = lean_unbox_usize(v_i_3184_);
lean_dec(v_i_3184_);
v_res_3188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3186_, v_i_boxed_3187_, v_bs_3185_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3189_, lean_object* v_data_3190_, lean_object* v_ref_3191_, lean_object* v_msg_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_toCold_3198_; lean_object* v_currRecDepth_3199_; lean_object* v_ref_3200_; uint16_t v_optionFlags_3201_; uint8_t v_suppressElabErrors_3202_; uint8_t v_isRecordingDeps_3203_; lean_object* v_ref_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v_traceState_3207_; lean_object* v_traces_3208_; lean_object* v___x_3209_; size_t v_sz_3210_; size_t v___x_3211_; lean_object* v___x_3212_; lean_object* v_msg_3213_; lean_object* v___x_3214_; lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3253_; 
v_toCold_3198_ = lean_ctor_get(v___y_3195_, 0);
v_currRecDepth_3199_ = lean_ctor_get(v___y_3195_, 1);
v_ref_3200_ = lean_ctor_get(v___y_3195_, 2);
v_optionFlags_3201_ = lean_ctor_get_uint16(v___y_3195_, sizeof(void*)*3);
v_suppressElabErrors_3202_ = lean_ctor_get_uint8(v___y_3195_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3203_ = lean_ctor_get_uint8(v___y_3195_, sizeof(void*)*3 + 3);
v_ref_3204_ = l_Lean_replaceRef(v_ref_3191_, v_ref_3200_);
lean_inc(v_currRecDepth_3199_);
lean_inc_ref(v_toCold_3198_);
v___x_3205_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3205_, 0, v_toCold_3198_);
lean_ctor_set(v___x_3205_, 1, v_currRecDepth_3199_);
lean_ctor_set(v___x_3205_, 2, v_ref_3204_);
lean_ctor_set_uint16(v___x_3205_, sizeof(void*)*3, v_optionFlags_3201_);
lean_ctor_set_uint8(v___x_3205_, sizeof(void*)*3 + 2, v_suppressElabErrors_3202_);
lean_ctor_set_uint8(v___x_3205_, sizeof(void*)*3 + 3, v_isRecordingDeps_3203_);
v___x_3206_ = lean_st_ref_get(v___y_3196_);
v_traceState_3207_ = lean_ctor_get(v___x_3206_, 4);
lean_inc_ref(v_traceState_3207_);
lean_dec(v___x_3206_);
v_traces_3208_ = lean_ctor_get(v_traceState_3207_, 0);
lean_inc_ref(v_traces_3208_);
lean_dec_ref(v_traceState_3207_);
v___x_3209_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3208_);
lean_dec_ref(v_traces_3208_);
v_sz_3210_ = lean_array_size(v___x_3209_);
v___x_3211_ = ((size_t)0ULL);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3210_, v___x_3211_, v___x_3209_);
v_msg_3213_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3213_, 0, v_data_3190_);
lean_ctor_set(v_msg_3213_, 1, v_msg_3192_);
lean_ctor_set(v_msg_3213_, 2, v___x_3212_);
v___x_3214_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3213_, v___y_3193_, v___y_3194_, v___x_3205_, v___y_3196_);
lean_dec_ref_known(v___x_3205_, 3);
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3253_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3253_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v_traceState_3220_; lean_object* v_env_3221_; lean_object* v_nextMacroScope_3222_; lean_object* v_ngen_3223_; lean_object* v_auxDeclNGen_3224_; lean_object* v_cache_3225_; lean_object* v_recordedDeps_3226_; lean_object* v_messages_3227_; lean_object* v_infoState_3228_; lean_object* v_snapshotTasks_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3252_; 
v___x_3219_ = lean_st_ref_take(v___y_3196_);
v_traceState_3220_ = lean_ctor_get(v___x_3219_, 4);
v_env_3221_ = lean_ctor_get(v___x_3219_, 0);
v_nextMacroScope_3222_ = lean_ctor_get(v___x_3219_, 1);
v_ngen_3223_ = lean_ctor_get(v___x_3219_, 2);
v_auxDeclNGen_3224_ = lean_ctor_get(v___x_3219_, 3);
v_cache_3225_ = lean_ctor_get(v___x_3219_, 5);
v_recordedDeps_3226_ = lean_ctor_get(v___x_3219_, 6);
v_messages_3227_ = lean_ctor_get(v___x_3219_, 7);
v_infoState_3228_ = lean_ctor_get(v___x_3219_, 8);
v_snapshotTasks_3229_ = lean_ctor_get(v___x_3219_, 9);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3231_ = v___x_3219_;
v_isShared_3232_ = v_isSharedCheck_3252_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_snapshotTasks_3229_);
lean_inc(v_infoState_3228_);
lean_inc(v_messages_3227_);
lean_inc(v_recordedDeps_3226_);
lean_inc(v_cache_3225_);
lean_inc(v_traceState_3220_);
lean_inc(v_auxDeclNGen_3224_);
lean_inc(v_ngen_3223_);
lean_inc(v_nextMacroScope_3222_);
lean_inc(v_env_3221_);
lean_dec(v___x_3219_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3252_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
uint64_t v_tid_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3250_; 
v_tid_3233_ = lean_ctor_get_uint64(v_traceState_3220_, sizeof(void*)*1);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_traceState_3220_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_traceState_3220_, 0);
lean_dec(v_unused_3251_);
v___x_3235_ = v_traceState_3220_;
v_isShared_3236_ = v_isSharedCheck_3250_;
goto v_resetjp_3234_;
}
else
{
lean_dec(v_traceState_3220_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3250_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3237_ = lean_box(0);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_ref_3191_);
lean_ctor_set(v___x_3238_, 1, v_a_3215_);
v___x_3239_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3189_, v___x_3238_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3239_);
v___x_3241_ = v___x_3235_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3239_);
lean_ctor_set_uint64(v_reuseFailAlloc_3249_, sizeof(void*)*1, v_tid_3233_);
v___x_3241_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3243_; 
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 4, v___x_3241_);
v___x_3243_ = v___x_3231_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_env_3221_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_nextMacroScope_3222_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_ngen_3223_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v_auxDeclNGen_3224_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3248_, 5, v_cache_3225_);
lean_ctor_set(v_reuseFailAlloc_3248_, 6, v_recordedDeps_3226_);
lean_ctor_set(v_reuseFailAlloc_3248_, 7, v_messages_3227_);
lean_ctor_set(v_reuseFailAlloc_3248_, 8, v_infoState_3228_);
lean_ctor_set(v_reuseFailAlloc_3248_, 9, v_snapshotTasks_3229_);
v___x_3243_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3244_ = lean_st_ref_put(v___y_3196_, v___x_3243_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3237_);
v___x_3246_ = v___x_3217_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3237_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3254_, lean_object* v_data_3255_, lean_object* v_ref_3256_, lean_object* v_msg_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3254_, v_data_3255_, v_ref_3256_, v_msg_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
return v_res_3263_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3266_ = l_Lean_stringToMessageData(v___x_3265_);
return v___x_3266_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3267_; double v___x_3268_; 
v___x_3267_ = lean_unsigned_to_nat(1000u);
v___x_3268_ = lean_float_of_nat(v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3269_, uint8_t v_collapsed_3270_, lean_object* v_tag_3271_, lean_object* v_opts_3272_, uint8_t v_clsEnabled_3273_, lean_object* v_oldTraces_3274_, lean_object* v_msg_3275_, lean_object* v_resStartStop_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_fst_3284_; lean_object* v_snd_3285_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v_data_3289_; lean_object* v_fst_3300_; lean_object* v_snd_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; lean_object* v___y_3305_; lean_object* v_a_3306_; uint8_t v___y_3321_; double v___y_3353_; 
v_fst_3284_ = lean_ctor_get(v_resStartStop_3276_, 0);
lean_inc(v_fst_3284_);
v_snd_3285_ = lean_ctor_get(v_resStartStop_3276_, 1);
lean_inc(v_snd_3285_);
lean_dec_ref(v_resStartStop_3276_);
v_fst_3300_ = lean_ctor_get(v_snd_3285_, 0);
lean_inc(v_fst_3300_);
v_snd_3301_ = lean_ctor_get(v_snd_3285_, 1);
lean_inc(v_snd_3301_);
lean_dec(v_snd_3285_);
v___x_3302_ = l_Lean_trace_profiler;
v___x_3303_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3272_, v___x_3302_);
if (v___x_3303_ == 0)
{
v___y_3321_ = v___x_3303_;
goto v___jp_3320_;
}
else
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3359_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3272_, v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; double v___x_3362_; double v___x_3363_; double v___x_3364_; 
v___x_3360_ = l_Lean_trace_profiler_threshold;
v___x_3361_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3272_, v___x_3360_);
v___x_3362_ = lean_float_of_nat(v___x_3361_);
v___x_3363_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3364_ = lean_float_div(v___x_3362_, v___x_3363_);
v___y_3353_ = v___x_3364_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; double v___x_3367_; 
v___x_3365_ = l_Lean_trace_profiler_threshold;
v___x_3366_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3272_, v___x_3365_);
v___x_3367_ = lean_float_of_nat(v___x_3366_);
v___y_3353_ = v___x_3367_;
goto v___jp_3352_;
}
}
v___jp_3286_:
{
lean_object* v___x_3290_; 
lean_inc(v___y_3287_);
v___x_3290_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3274_, v_data_3289_, v___y_3287_, v___y_3288_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3291_; 
lean_dec_ref_known(v___x_3290_, 1);
v___x_3291_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3284_);
return v___x_3291_;
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec(v_fst_3284_);
v_a_3292_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3290_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3290_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
v___jp_3304_:
{
uint8_t v_result_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; double v___x_3310_; lean_object* v_data_3311_; 
v_result_3307_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3284_);
v___x_3308_ = lean_box(v_result_3307_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
v___x_3310_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3271_);
lean_inc_ref(v___x_3309_);
lean_inc(v_cls_3269_);
v_data_3311_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3311_, 0, v_cls_3269_);
lean_ctor_set(v_data_3311_, 1, v___x_3309_);
lean_ctor_set(v_data_3311_, 2, v_tag_3271_);
lean_ctor_set_float(v_data_3311_, sizeof(void*)*3, v___x_3310_);
lean_ctor_set_float(v_data_3311_, sizeof(void*)*3 + 8, v___x_3310_);
lean_ctor_set_uint8(v_data_3311_, sizeof(void*)*3 + 16, v_collapsed_3270_);
if (v___x_3303_ == 0)
{
lean_dec_ref_known(v___x_3309_, 1);
lean_dec(v_snd_3301_);
lean_dec(v_fst_3300_);
lean_dec_ref(v_tag_3271_);
lean_dec(v_cls_3269_);
v___y_3287_ = v___y_3305_;
v___y_3288_ = v_a_3306_;
v_data_3289_ = v_data_3311_;
goto v___jp_3286_;
}
else
{
lean_object* v_data_3312_; double v___x_3313_; double v___x_3314_; 
lean_dec_ref_known(v_data_3311_, 3);
v_data_3312_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3312_, 0, v_cls_3269_);
lean_ctor_set(v_data_3312_, 1, v___x_3309_);
lean_ctor_set(v_data_3312_, 2, v_tag_3271_);
v___x_3313_ = lean_unbox_float(v_fst_3300_);
lean_dec(v_fst_3300_);
lean_ctor_set_float(v_data_3312_, sizeof(void*)*3, v___x_3313_);
v___x_3314_ = lean_unbox_float(v_snd_3301_);
lean_dec(v_snd_3301_);
lean_ctor_set_float(v_data_3312_, sizeof(void*)*3 + 8, v___x_3314_);
lean_ctor_set_uint8(v_data_3312_, sizeof(void*)*3 + 16, v_collapsed_3270_);
v___y_3287_ = v___y_3305_;
v___y_3288_ = v_a_3306_;
v_data_3289_ = v_data_3312_;
goto v___jp_3286_;
}
}
v___jp_3315_:
{
lean_object* v_ref_3316_; lean_object* v___x_3317_; 
v_ref_3316_ = lean_ctor_get(v___y_3281_, 2);
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3281_);
lean_inc(v___y_3280_);
lean_inc_ref(v___y_3279_);
lean_inc(v___y_3278_);
lean_inc(v___y_3277_);
lean_inc(v_fst_3284_);
v___x_3317_ = lean_apply_8(v_msg_3275_, v_fst_3284_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, lean_box(0));
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___y_3305_ = v_ref_3316_;
v_a_3306_ = v_a_3318_;
goto v___jp_3304_;
}
else
{
lean_object* v___x_3319_; 
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3305_ = v_ref_3316_;
v_a_3306_ = v___x_3319_;
goto v___jp_3304_;
}
}
v___jp_3320_:
{
if (v_clsEnabled_3273_ == 0)
{
if (v___y_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v_traceState_3323_; lean_object* v_env_3324_; lean_object* v_nextMacroScope_3325_; lean_object* v_ngen_3326_; lean_object* v_auxDeclNGen_3327_; lean_object* v_cache_3328_; lean_object* v_recordedDeps_3329_; lean_object* v_messages_3330_; lean_object* v_infoState_3331_; lean_object* v_snapshotTasks_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v_snd_3301_);
lean_dec(v_fst_3300_);
lean_dec_ref(v_msg_3275_);
lean_dec_ref(v_tag_3271_);
lean_dec(v_cls_3269_);
v___x_3322_ = lean_st_ref_take(v___y_3282_);
v_traceState_3323_ = lean_ctor_get(v___x_3322_, 4);
v_env_3324_ = lean_ctor_get(v___x_3322_, 0);
v_nextMacroScope_3325_ = lean_ctor_get(v___x_3322_, 1);
v_ngen_3326_ = lean_ctor_get(v___x_3322_, 2);
v_auxDeclNGen_3327_ = lean_ctor_get(v___x_3322_, 3);
v_cache_3328_ = lean_ctor_get(v___x_3322_, 5);
v_recordedDeps_3329_ = lean_ctor_get(v___x_3322_, 6);
v_messages_3330_ = lean_ctor_get(v___x_3322_, 7);
v_infoState_3331_ = lean_ctor_get(v___x_3322_, 8);
v_snapshotTasks_3332_ = lean_ctor_get(v___x_3322_, 9);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3334_ = v___x_3322_;
v_isShared_3335_ = v_isSharedCheck_3351_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_snapshotTasks_3332_);
lean_inc(v_infoState_3331_);
lean_inc(v_messages_3330_);
lean_inc(v_recordedDeps_3329_);
lean_inc(v_cache_3328_);
lean_inc(v_traceState_3323_);
lean_inc(v_auxDeclNGen_3327_);
lean_inc(v_ngen_3326_);
lean_inc(v_nextMacroScope_3325_);
lean_inc(v_env_3324_);
lean_dec(v___x_3322_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3351_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
uint64_t v_tid_3336_; lean_object* v_traces_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3350_; 
v_tid_3336_ = lean_ctor_get_uint64(v_traceState_3323_, sizeof(void*)*1);
v_traces_3337_ = lean_ctor_get(v_traceState_3323_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_traceState_3323_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3339_ = v_traceState_3323_;
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_traces_3337_);
lean_dec(v_traceState_3323_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3341_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3274_, v_traces_3337_);
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
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_env_3324_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_nextMacroScope_3325_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_ngen_3326_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_auxDeclNGen_3327_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3348_, 5, v_cache_3328_);
lean_ctor_set(v_reuseFailAlloc_3348_, 6, v_recordedDeps_3329_);
lean_ctor_set(v_reuseFailAlloc_3348_, 7, v_messages_3330_);
lean_ctor_set(v_reuseFailAlloc_3348_, 8, v_infoState_3331_);
lean_ctor_set(v_reuseFailAlloc_3348_, 9, v_snapshotTasks_3332_);
v___x_3345_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_st_ref_put(v___y_3282_, v___x_3345_);
v___x_3347_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3284_);
return v___x_3347_;
}
}
}
}
}
else
{
goto v___jp_3315_;
}
}
else
{
goto v___jp_3315_;
}
}
v___jp_3352_:
{
double v___x_3354_; double v___x_3355_; double v___x_3356_; uint8_t v___x_3357_; 
v___x_3354_ = lean_unbox_float(v_snd_3301_);
v___x_3355_ = lean_unbox_float(v_fst_3300_);
v___x_3356_ = lean_float_sub(v___x_3354_, v___x_3355_);
v___x_3357_ = lean_float_decLt(v___y_3353_, v___x_3356_);
v___y_3321_ = v___x_3357_;
goto v___jp_3320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3368_, lean_object* v_collapsed_3369_, lean_object* v_tag_3370_, lean_object* v_opts_3371_, lean_object* v_clsEnabled_3372_, lean_object* v_oldTraces_3373_, lean_object* v_msg_3374_, lean_object* v_resStartStop_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
uint8_t v_collapsed_boxed_3383_; uint8_t v_clsEnabled_boxed_3384_; lean_object* v_res_3385_; 
v_collapsed_boxed_3383_ = lean_unbox(v_collapsed_3369_);
v_clsEnabled_boxed_3384_ = lean_unbox(v_clsEnabled_3372_);
v_res_3385_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3368_, v_collapsed_boxed_3383_, v_tag_3370_, v_opts_3371_, v_clsEnabled_boxed_3384_, v_oldTraces_3373_, v_msg_3374_, v_resStartStop_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v_opts_3371_);
return v_res_3385_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_unsigned_to_nat(32u);
v___x_3387_ = lean_mk_empty_array_with_capacity(v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3389_ = ((size_t)5ULL);
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = lean_unsigned_to_nat(32u);
v___x_3392_ = lean_mk_empty_array_with_capacity(v___x_3391_);
v___x_3393_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3394_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___x_3392_);
lean_ctor_set(v___x_3394_, 2, v___x_3390_);
lean_ctor_set(v___x_3394_, 3, v___x_3390_);
lean_ctor_set_usize(v___x_3394_, 4, v___x_3389_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3395_){
_start:
{
lean_object* v___x_3397_; lean_object* v_traceState_3398_; lean_object* v_traces_3399_; lean_object* v___x_3400_; lean_object* v_traceState_3401_; lean_object* v_env_3402_; lean_object* v_nextMacroScope_3403_; lean_object* v_ngen_3404_; lean_object* v_auxDeclNGen_3405_; lean_object* v_cache_3406_; lean_object* v_recordedDeps_3407_; lean_object* v_messages_3408_; lean_object* v_infoState_3409_; lean_object* v_snapshotTasks_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3429_; 
v___x_3397_ = lean_st_ref_get(v___y_3395_);
v_traceState_3398_ = lean_ctor_get(v___x_3397_, 4);
lean_inc_ref(v_traceState_3398_);
lean_dec(v___x_3397_);
v_traces_3399_ = lean_ctor_get(v_traceState_3398_, 0);
lean_inc_ref(v_traces_3399_);
lean_dec_ref(v_traceState_3398_);
v___x_3400_ = lean_st_ref_take(v___y_3395_);
v_traceState_3401_ = lean_ctor_get(v___x_3400_, 4);
v_env_3402_ = lean_ctor_get(v___x_3400_, 0);
v_nextMacroScope_3403_ = lean_ctor_get(v___x_3400_, 1);
v_ngen_3404_ = lean_ctor_get(v___x_3400_, 2);
v_auxDeclNGen_3405_ = lean_ctor_get(v___x_3400_, 3);
v_cache_3406_ = lean_ctor_get(v___x_3400_, 5);
v_recordedDeps_3407_ = lean_ctor_get(v___x_3400_, 6);
v_messages_3408_ = lean_ctor_get(v___x_3400_, 7);
v_infoState_3409_ = lean_ctor_get(v___x_3400_, 8);
v_snapshotTasks_3410_ = lean_ctor_get(v___x_3400_, 9);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3412_ = v___x_3400_;
v_isShared_3413_ = v_isSharedCheck_3429_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_snapshotTasks_3410_);
lean_inc(v_infoState_3409_);
lean_inc(v_messages_3408_);
lean_inc(v_recordedDeps_3407_);
lean_inc(v_cache_3406_);
lean_inc(v_traceState_3401_);
lean_inc(v_auxDeclNGen_3405_);
lean_inc(v_ngen_3404_);
lean_inc(v_nextMacroScope_3403_);
lean_inc(v_env_3402_);
lean_dec(v___x_3400_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3429_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
uint64_t v_tid_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3427_; 
v_tid_3414_ = lean_ctor_get_uint64(v_traceState_3401_, sizeof(void*)*1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_traceState_3401_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v_traceState_3401_, 0);
lean_dec(v_unused_3428_);
v___x_3416_ = v_traceState_3401_;
v_isShared_3417_ = v_isSharedCheck_3427_;
goto v_resetjp_3415_;
}
else
{
lean_dec(v_traceState_3401_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3427_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3418_);
lean_ctor_set_uint64(v_reuseFailAlloc_3426_, sizeof(void*)*1, v_tid_3414_);
v___x_3420_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 4, v___x_3420_);
v___x_3422_ = v___x_3412_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_env_3402_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_nextMacroScope_3403_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_ngen_3404_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_auxDeclNGen_3405_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3425_, 5, v_cache_3406_);
lean_ctor_set(v_reuseFailAlloc_3425_, 6, v_recordedDeps_3407_);
lean_ctor_set(v_reuseFailAlloc_3425_, 7, v_messages_3408_);
lean_ctor_set(v_reuseFailAlloc_3425_, 8, v_infoState_3409_);
lean_ctor_set(v_reuseFailAlloc_3425_, 9, v_snapshotTasks_3410_);
v___x_3422_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_st_ref_put(v___y_3395_, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v_traces_3399_);
return v___x_3424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3430_);
lean_dec(v___y_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; 
lean_inc(v___y_3435_);
lean_inc(v___y_3434_);
v___x_3441_ = lean_apply_7(v_x_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, lean_box(0));
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3451_, lean_object* v_localInsts_3452_, lean_object* v_x_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v___f_3461_; lean_object* v___x_3462_; 
lean_inc(v___y_3455_);
lean_inc(v___y_3454_);
v___f_3461_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3461_, 0, v_x_3453_);
lean_closure_set(v___f_3461_, 1, v___y_3454_);
lean_closure_set(v___f_3461_, 2, v___y_3455_);
v___x_3462_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3451_, v_localInsts_3452_, v___f_3461_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3462_) == 0)
{
return v___x_3462_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3471_, lean_object* v_localInsts_3472_, lean_object* v_x_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3471_, v_localInsts_3472_, v_x_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec(v___y_3474_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; lean_object* v_ngen_3485_; lean_object* v_namePrefix_3486_; lean_object* v_idx_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3517_; 
v___x_3484_ = lean_st_ref_get(v___y_3482_);
v_ngen_3485_ = lean_ctor_get(v___x_3484_, 2);
lean_inc_ref(v_ngen_3485_);
lean_dec(v___x_3484_);
v_namePrefix_3486_ = lean_ctor_get(v_ngen_3485_, 0);
v_idx_3487_ = lean_ctor_get(v_ngen_3485_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_ngen_3485_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3489_ = v_ngen_3485_;
v_isShared_3490_ = v_isSharedCheck_3517_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_idx_3487_);
lean_inc(v_namePrefix_3486_);
lean_dec(v_ngen_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3517_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_r_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_inc(v_idx_3487_);
lean_inc(v_namePrefix_3486_);
v_r_3491_ = l_Lean_Name_num___override(v_namePrefix_3486_, v_idx_3487_);
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = lean_nat_add(v_idx_3487_, v___x_3492_);
lean_dec(v_idx_3487_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v___x_3493_);
v___x_3495_ = v___x_3489_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_namePrefix_3486_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3496_; lean_object* v_env_3497_; lean_object* v_nextMacroScope_3498_; lean_object* v_auxDeclNGen_3499_; lean_object* v_traceState_3500_; lean_object* v_cache_3501_; lean_object* v_recordedDeps_3502_; lean_object* v_messages_3503_; lean_object* v_infoState_3504_; lean_object* v_snapshotTasks_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3514_; 
v___x_3496_ = lean_st_ref_take(v___y_3482_);
v_env_3497_ = lean_ctor_get(v___x_3496_, 0);
v_nextMacroScope_3498_ = lean_ctor_get(v___x_3496_, 1);
v_auxDeclNGen_3499_ = lean_ctor_get(v___x_3496_, 3);
v_traceState_3500_ = lean_ctor_get(v___x_3496_, 4);
v_cache_3501_ = lean_ctor_get(v___x_3496_, 5);
v_recordedDeps_3502_ = lean_ctor_get(v___x_3496_, 6);
v_messages_3503_ = lean_ctor_get(v___x_3496_, 7);
v_infoState_3504_ = lean_ctor_get(v___x_3496_, 8);
v_snapshotTasks_3505_ = lean_ctor_get(v___x_3496_, 9);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3514_ == 0)
{
lean_object* v_unused_3515_; 
v_unused_3515_ = lean_ctor_get(v___x_3496_, 2);
lean_dec(v_unused_3515_);
v___x_3507_ = v___x_3496_;
v_isShared_3508_ = v_isSharedCheck_3514_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_snapshotTasks_3505_);
lean_inc(v_infoState_3504_);
lean_inc(v_messages_3503_);
lean_inc(v_recordedDeps_3502_);
lean_inc(v_cache_3501_);
lean_inc(v_traceState_3500_);
lean_inc(v_auxDeclNGen_3499_);
lean_inc(v_nextMacroScope_3498_);
lean_inc(v_env_3497_);
lean_dec(v___x_3496_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3514_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 2, v___x_3495_);
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_env_3497_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_nextMacroScope_3498_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3513_, 3, v_auxDeclNGen_3499_);
lean_ctor_set(v_reuseFailAlloc_3513_, 4, v_traceState_3500_);
lean_ctor_set(v_reuseFailAlloc_3513_, 5, v_cache_3501_);
lean_ctor_set(v_reuseFailAlloc_3513_, 6, v_recordedDeps_3502_);
lean_ctor_set(v_reuseFailAlloc_3513_, 7, v_messages_3503_);
lean_ctor_set(v_reuseFailAlloc_3513_, 8, v_infoState_3504_);
lean_ctor_set(v_reuseFailAlloc_3513_, 9, v_snapshotTasks_3505_);
v___x_3510_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_st_ref_put(v___y_3482_, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v_r_3491_);
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
lean_object* v_keyedConfig_3595_; uint8_t v_trackZetaDelta_3596_; lean_object* v_zetaDeltaSet_3597_; lean_object* v_localInstances_3598_; lean_object* v_defEqCtx_x3f_3599_; lean_object* v_synthPendingDepth_3600_; lean_object* v_customCanUnfoldPredicate_x3f_3601_; uint8_t v_univApprox_3602_; uint8_t v_inTypeClassResolution_3603_; uint8_t v_cacheInferType_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_keyedConfig_3595_ = lean_ctor_get(v___y_3590_, 0);
v_trackZetaDelta_3596_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7);
v_zetaDeltaSet_3597_ = lean_ctor_get(v___y_3590_, 1);
v_localInstances_3598_ = lean_ctor_get(v___y_3590_, 3);
v_defEqCtx_x3f_3599_ = lean_ctor_get(v___y_3590_, 4);
v_synthPendingDepth_3600_ = lean_ctor_get(v___y_3590_, 5);
v_customCanUnfoldPredicate_x3f_3601_ = lean_ctor_get(v___y_3590_, 6);
v_univApprox_3602_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3603_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7 + 2);
v_cacheInferType_3604_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3601_);
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
lean_ctor_set(v___x_3605_, 6, v_customCanUnfoldPredicate_x3f_3601_);
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
v___x_3683_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3670_, v_expr_3671_, v___x_3681_, v___x_3682_, v___y_3664_);
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
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3779_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3779_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3779_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_expr_3761_; size_t v___x_3762_; size_t v___x_3763_; uint8_t v___x_3764_; 
v_expr_3761_ = lean_ctor_get(v_a_3757_, 0);
lean_inc_ref(v_expr_3761_);
lean_dec(v_a_3757_);
v___x_3762_ = lean_ptr_addr(v_fn_3752_);
v___x_3763_ = lean_ptr_addr(v_a_3755_);
v___x_3764_ = lean_usize_dec_eq(v___x_3762_, v___x_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec_ref_known(v_e_3744_, 2);
v___x_3765_ = l_Lean_Expr_app___override(v_a_3755_, v_expr_3761_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3765_);
v___x_3767_ = v___x_3759_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
else
{
size_t v___x_3769_; size_t v___x_3770_; uint8_t v___x_3771_; 
v___x_3769_ = lean_ptr_addr(v_arg_3753_);
v___x_3770_ = lean_ptr_addr(v_expr_3761_);
v___x_3771_ = lean_usize_dec_eq(v___x_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3774_; 
lean_dec_ref_known(v_e_3744_, 2);
v___x_3772_ = l_Lean_Expr_app___override(v_a_3755_, v_expr_3761_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3772_);
v___x_3774_ = v___x_3759_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
else
{
lean_object* v___x_3777_; 
lean_dec_ref(v_expr_3761_);
lean_dec(v_a_3755_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_e_3744_);
v___x_3777_ = v___x_3759_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_e_3744_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v_a_3755_);
lean_dec_ref_known(v_e_3744_, 2);
v_a_3780_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3756_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3756_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
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
lean_object* v___x_3788_; 
v___x_3788_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3797_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3797_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3797_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v_expr_3793_; lean_object* v___x_3795_; 
v_expr_3793_ = lean_ctor_get(v_a_3789_, 0);
lean_inc_ref(v_expr_3793_);
lean_dec(v_a_3789_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v_expr_3793_);
v___x_3795_ = v___x_3791_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_expr_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v_a_3798_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3788_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3788_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec(v_a_3808_);
lean_dec(v_a_3807_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
if (lean_obj_tag(v_e_3815_) == 5)
{
lean_object* v_fn_3823_; lean_object* v_arg_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v_fn_3823_ = lean_ctor_get(v_e_3815_, 0);
v_arg_3824_ = lean_ctor_get(v_e_3815_, 1);
lean_inc_ref_n(v_fn_3823_, 2);
v___x_3825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3825_, 0, v_fn_3823_);
v___x_3826_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3823_, v___x_3825_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3828_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
lean_inc_ref(v_arg_3824_);
v___x_3828_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3824_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3828_, 1);
v___x_3830_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3815_, v_a_3827_, v_a_3829_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
return v___x_3830_;
}
else
{
lean_dec(v_a_3827_);
lean_dec_ref_known(v_e_3815_, 2);
return v___x_3828_;
}
}
else
{
lean_dec_ref_known(v_e_3815_, 2);
return v___x_3826_;
}
}
else
{
lean_object* v___x_3831_; 
v___x_3831_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
return v___x_3831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
uint8_t v___x_3840_; 
v___x_3840_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3833_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
v___x_3841_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3851_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3844_ = v___x_3841_;
v_isShared_3845_ = v_isSharedCheck_3851_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3841_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3851_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3846_ = lean_box(0);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_a_3842_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v___x_3847_);
v___x_3849_ = v___x_3844_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
v_a_3852_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3841_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3841_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_Expr_getAppFn(v_e_3832_);
if (lean_obj_tag(v___x_3860_) == 2)
{
lean_object* v_mvarId_3861_; lean_object* v_dummy_3862_; lean_object* v_nargs_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v_mvarId_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_mvarId_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v_dummy_3862_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3863_ = l_Lean_Expr_getAppNumArgs(v_e_3832_);
lean_inc(v_nargs_3863_);
v___x_3864_ = lean_mk_array(v_nargs_3863_, v_dummy_3862_);
v___x_3865_ = lean_unsigned_to_nat(1u);
v___x_3866_ = lean_nat_sub(v_nargs_3863_, v___x_3865_);
lean_dec(v_nargs_3863_);
lean_inc_ref(v_e_3832_);
v___x_3867_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3832_, v___x_3864_, v___x_3866_);
v___x_3868_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3861_, v___x_3867_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_mvarId_3861_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v___x_3869_; 
lean_dec_ref_known(v___x_3868_, 1);
v___x_3869_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
return v___x_3869_;
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec_ref(v_e_3832_);
v_a_3870_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3868_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3868_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v___x_3878_; 
lean_dec_ref(v___x_3860_);
v___x_3878_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
return v___x_3878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
lean_dec(v_a_3880_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3897_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
return v___x_3898_;
}
else
{
return v___x_3896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec(v_a_3900_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3908_, lean_object* v_fvars_3909_, lean_object* v_doms_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3908_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3909_, v_doms_3910_, v_a_3919_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
return v___x_3920_;
}
else
{
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3921_, lean_object* v_fvars_3922_, lean_object* v_doms_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3921_, v_fvars_3922_, v_doms_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v_doms_3923_);
lean_dec_ref(v_fvars_3922_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3932_, lean_object* v_fvars_3933_, lean_object* v_doms_3934_, lean_object* v_e_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3935_, v_a_3937_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
if (lean_obj_tag(v_a_3944_) == 1)
{
lean_object* v_val_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
lean_dec_ref(v_e_3935_);
v_val_3945_ = lean_ctor_get(v_a_3944_, 0);
lean_inc(v_val_3945_);
lean_dec_ref_known(v_a_3944_, 1);
v___x_3946_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3947_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3947_, 0, v_fvars_3933_);
lean_closure_set(v___x_3947_, 1, v_doms_3934_);
lean_closure_set(v___x_3947_, 2, v_val_3945_);
v___x_3948_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3932_, v___x_3946_, v___x_3947_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
return v___x_3948_;
}
else
{
lean_dec(v_a_3944_);
if (lean_obj_tag(v_e_3935_) == 7)
{
lean_object* v_binderName_3949_; lean_object* v_binderType_3950_; lean_object* v_body_3951_; uint8_t v_binderInfo_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_binderName_3949_ = lean_ctor_get(v_e_3935_, 0);
lean_inc(v_binderName_3949_);
v_binderType_3950_ = lean_ctor_get(v_e_3935_, 1);
lean_inc_ref(v_binderType_3950_);
v_body_3951_ = lean_ctor_get(v_e_3935_, 2);
lean_inc_ref(v_body_3951_);
v_binderInfo_3952_ = lean_ctor_get_uint8(v_e_3935_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3935_, 3);
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3954_ = lean_expr_instantiate_rev(v_binderType_3950_, v_fvars_3933_);
lean_dec_ref(v_binderType_3950_);
v___x_3955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3955_, 0, v___x_3954_);
lean_inc_ref(v_lctx_3932_);
v___x_3956_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3932_, v___x_3953_, v___x_3955_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3958_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v___x_3958_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v_expr_3960_; uint8_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc_n(v_a_3959_, 2);
lean_dec_ref_known(v___x_3958_, 1);
v_expr_3960_ = lean_ctor_get(v_a_3957_, 0);
v___x_3961_ = 0;
lean_inc_ref(v_expr_3960_);
v___x_3962_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3932_, v_a_3959_, v_binderName_3949_, v_expr_3960_, v_binderInfo_3952_, v___x_3961_);
v___x_3963_ = l_Lean_Expr_fvar___override(v_a_3959_);
v___x_3964_ = lean_array_push(v_fvars_3933_, v___x_3963_);
v___x_3965_ = lean_array_push(v_doms_3934_, v_a_3957_);
v_lctx_3932_ = v___x_3962_;
v_fvars_3933_ = v___x_3964_;
v_doms_3934_ = v___x_3965_;
v_e_3935_ = v_body_3951_;
goto _start;
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v_a_3957_);
lean_dec_ref(v_body_3951_);
lean_dec(v_binderName_3949_);
lean_dec_ref(v_doms_3934_);
lean_dec_ref(v_fvars_3933_);
lean_dec_ref(v_lctx_3932_);
v_a_3967_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3958_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3958_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
else
{
lean_dec_ref(v_body_3951_);
lean_dec(v_binderName_3949_);
lean_dec_ref(v_doms_3934_);
lean_dec_ref(v_fvars_3933_);
lean_dec_ref(v_lctx_3932_);
return v___x_3956_;
}
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___f_3977_; lean_object* v___x_3978_; 
v___x_3975_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3976_ = lean_expr_instantiate_rev(v_e_3935_, v_fvars_3933_);
lean_dec_ref(v_e_3935_);
v___f_3977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3977_, 0, v___x_3976_);
lean_closure_set(v___f_3977_, 1, v_fvars_3933_);
lean_closure_set(v___f_3977_, 2, v_doms_3934_);
v___x_3978_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3932_, v___x_3975_, v___f_3977_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
return v___x_3978_;
}
}
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec_ref(v_e_3935_);
lean_dec_ref(v_doms_3934_);
lean_dec_ref(v_fvars_3933_);
lean_dec_ref(v_lctx_3932_);
v_a_3979_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3943_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3943_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
uint32_t v___x_3995_; uint8_t v___x_3996_; 
v___x_3995_ = 5;
v___x_3996_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3987_, v___x_3995_);
if (v___x_3996_ == 0)
{
lean_object* v_lctx_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_lctx_3997_ = lean_ctor_get(v_a_3990_, 2);
v___x_3998_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3997_);
v___x_3999_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3997_, v___x_3998_, v___x_3998_, v_e_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
return v___x_3999_;
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = lean_box(0);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v_e_3987_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec(v_a_4004_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_4012_, lean_object* v_e_4013_, lean_object* v_typeName_4014_, lean_object* v_idx_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4012_, v_e_4013_, v_typeName_4014_, v_idx_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec(v___y_4016_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_a_4026_);
lean_dec(v_a_4025_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4044_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 1);
v___x_4044_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4033_, v_a_4043_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4044_;
}
else
{
lean_dec_ref(v_fvars_4033_);
return v___x_4042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec(v___y_4047_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4055_, lean_object* v_fvars_4056_, lean_object* v_e_4057_, lean_object* v_letFVars_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_){
_start:
{
switch(lean_obj_tag(v_e_4057_))
{
case 6:
{
lean_object* v_binderName_4066_; lean_object* v_binderType_4067_; lean_object* v_body_4068_; uint8_t v_binderInfo_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_binderName_4066_ = lean_ctor_get(v_e_4057_, 0);
lean_inc(v_binderName_4066_);
v_binderType_4067_ = lean_ctor_get(v_e_4057_, 1);
lean_inc_ref(v_binderType_4067_);
v_body_4068_ = lean_ctor_get(v_e_4057_, 2);
lean_inc_ref(v_body_4068_);
v_binderInfo_4069_ = lean_ctor_get_uint8(v_e_4057_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4057_, 3);
v___x_4070_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4055_);
lean_inc(v_letFVars_4058_);
v___x_4071_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4056_, v_letFVars_4058_, v_lctx_4055_, v___x_4070_, v_binderType_4067_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec_ref(v_binderType_4067_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v_expr_4075_; uint8_t v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc_n(v_a_4074_, 2);
lean_dec_ref_known(v___x_4073_, 1);
v_expr_4075_ = lean_ctor_get(v_a_4072_, 0);
lean_inc_ref(v_expr_4075_);
lean_dec(v_a_4072_);
v___x_4076_ = 0;
v___x_4077_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4055_, v_a_4074_, v_binderName_4066_, v_expr_4075_, v_binderInfo_4069_, v___x_4076_);
v___x_4078_ = l_Lean_Expr_fvar___override(v_a_4074_);
v___x_4079_ = lean_array_push(v_fvars_4056_, v___x_4078_);
v_lctx_4055_ = v___x_4077_;
v_fvars_4056_ = v___x_4079_;
v_e_4057_ = v_body_4068_;
goto _start;
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4072_);
lean_dec_ref(v_body_4068_);
lean_dec(v_binderName_4066_);
lean_dec(v_letFVars_4058_);
lean_dec_ref(v_fvars_4056_);
lean_dec_ref(v_lctx_4055_);
v_a_4081_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4073_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4073_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_dec_ref(v_body_4068_);
lean_dec(v_binderName_4066_);
lean_dec(v_letFVars_4058_);
lean_dec_ref(v_fvars_4056_);
lean_dec_ref(v_lctx_4055_);
return v___x_4071_;
}
}
case 8:
{
lean_object* v_declName_4089_; lean_object* v_type_4090_; lean_object* v_value_4091_; lean_object* v_body_4092_; uint8_t v_nondep_4093_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_declName_4089_ = lean_ctor_get(v_e_4057_, 0);
lean_inc(v_declName_4089_);
v_type_4090_ = lean_ctor_get(v_e_4057_, 1);
lean_inc_ref(v_type_4090_);
v_value_4091_ = lean_ctor_get(v_e_4057_, 2);
lean_inc_ref(v_value_4091_);
v_body_4092_ = lean_ctor_get(v_e_4057_, 3);
lean_inc_ref(v_body_4092_);
v_nondep_4093_ = lean_ctor_get_uint8(v_e_4057_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4057_, 4);
v___x_4107_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4055_);
lean_inc(v_letFVars_4058_);
v___x_4108_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4056_, v_letFVars_4058_, v_lctx_4055_, v___x_4107_, v_type_4090_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec_ref(v_type_4090_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___x_4108_, 1);
v___x_4110_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4055_);
lean_inc(v_letFVars_4058_);
v___x_4111_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4056_, v_letFVars_4058_, v_lctx_4055_, v___x_4110_, v_value_4091_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec_ref(v_value_4091_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; uint8_t v___x_4142_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4142_ = l_List_isEmpty___redArg(v_letFVars_4058_);
if (v___x_4142_ == 0)
{
lean_object* v___f_4143_; lean_object* v___x_4144_; 
lean_inc(v_a_4109_);
lean_inc(v_a_4112_);
v___f_4143_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4143_, 0, v_a_4112_);
lean_closure_set(v___f_4143_, 1, v_a_4109_);
lean_inc_ref(v_lctx_4055_);
v___x_4144_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4055_, v___f_4143_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_dec_ref_known(v___x_4144_, 1);
v___y_4114_ = v_a_4059_;
v___y_4115_ = v_a_4060_;
v___y_4116_ = v_a_4061_;
v___y_4117_ = v_a_4062_;
v___y_4118_ = v_a_4063_;
v___y_4119_ = v_a_4064_;
goto v___jp_4113_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v_a_4112_);
lean_dec(v_a_4109_);
lean_dec_ref(v_body_4092_);
lean_dec(v_declName_4089_);
lean_dec(v_letFVars_4058_);
lean_dec_ref(v_fvars_4056_);
lean_dec_ref(v_lctx_4055_);
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
v___y_4114_ = v_a_4059_;
v___y_4115_ = v_a_4060_;
v___y_4116_ = v_a_4061_;
v___y_4117_ = v_a_4062_;
v___y_4118_ = v_a_4063_;
v___y_4119_ = v_a_4064_;
goto v___jp_4113_;
}
v___jp_4113_:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v_expr_4122_; lean_object* v_expr_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4132_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
v_expr_4122_ = lean_ctor_get(v_a_4109_, 0);
lean_inc_ref(v_expr_4122_);
lean_dec(v_a_4109_);
v_expr_4123_ = lean_ctor_get(v_a_4112_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_a_4112_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; 
v_unused_4133_ = lean_ctor_get(v_a_4112_, 1);
lean_dec(v_unused_4133_);
v___x_4125_ = v_a_4112_;
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_expr_4123_);
lean_dec(v_a_4112_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
uint8_t v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = 0;
lean_inc(v_a_4121_);
v___x_4128_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4055_, v_a_4121_, v_declName_4089_, v_expr_4122_, v_expr_4123_, v_nondep_4093_, v___x_4127_);
if (v_nondep_4093_ == 0)
{
lean_object* v___x_4130_; 
lean_inc(v_a_4121_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set_tag(v___x_4125_, 1);
lean_ctor_set(v___x_4125_, 1, v_letFVars_4058_);
lean_ctor_set(v___x_4125_, 0, v_a_4121_);
v___x_4130_ = v___x_4125_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4121_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_letFVars_4058_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
v___y_4095_ = v___y_4115_;
v___y_4096_ = v___y_4114_;
v___y_4097_ = v_a_4121_;
v___y_4098_ = v___y_4118_;
v___y_4099_ = v___y_4117_;
v___y_4100_ = v___y_4116_;
v___y_4101_ = v___x_4128_;
v___y_4102_ = v___y_4119_;
v___y_4103_ = v___x_4130_;
goto v___jp_4094_;
}
}
else
{
lean_del_object(v___x_4125_);
v___y_4095_ = v___y_4115_;
v___y_4096_ = v___y_4114_;
v___y_4097_ = v_a_4121_;
v___y_4098_ = v___y_4118_;
v___y_4099_ = v___y_4117_;
v___y_4100_ = v___y_4116_;
v___y_4101_ = v___x_4128_;
v___y_4102_ = v___y_4119_;
v___y_4103_ = v_letFVars_4058_;
goto v___jp_4094_;
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec(v_a_4112_);
lean_dec(v_a_4109_);
lean_dec_ref(v_body_4092_);
lean_dec(v_declName_4089_);
lean_dec(v_letFVars_4058_);
lean_dec_ref(v_fvars_4056_);
lean_dec_ref(v_lctx_4055_);
v_a_4134_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4120_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4120_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
else
{
lean_dec(v_a_4109_);
lean_dec_ref(v_body_4092_);
lean_dec(v_declName_4089_);
lean_dec(v_letFVars_4058_);
lean_dec_ref(v_fvars_4056_);
lean_dec_ref(v_lctx_4055_);
return v___x_4111_;
}
}
else
{
lean_dec_ref(v_body_4092_);
lean_dec_ref(v_value_4091_);
lean_dec(v_declName_4089_);
lean_dec(v_letFVars_4058_);
lean_dec_ref(v_fvars_4056_);
lean_dec_ref(v_lctx_4055_);
return v___x_4108_;
}
v___jp_4094_:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = l_Lean_Expr_fvar___override(v___y_4097_);
v___x_4105_ = lean_array_push(v_fvars_4056_, v___x_4104_);
v_lctx_4055_ = v___y_4101_;
v_fvars_4056_ = v___x_4105_;
v_e_4057_ = v_body_4092_;
v_letFVars_4058_ = v___y_4103_;
v_a_4059_ = v___y_4096_;
v_a_4060_ = v___y_4095_;
v_a_4061_ = v___y_4100_;
v_a_4062_ = v___y_4099_;
v_a_4063_ = v___y_4098_;
v_a_4064_ = v___y_4102_;
goto _start;
}
}
default: 
{
lean_object* v___f_4153_; lean_object* v___x_4154_; 
lean_inc_ref(v_fvars_4056_);
v___f_4153_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4153_, 0, v_fvars_4056_);
v___x_4154_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4056_, v_letFVars_4058_, v_lctx_4055_, v___f_4153_, v_e_4057_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec_ref(v_e_4057_);
lean_dec_ref(v_fvars_4056_);
return v___x_4154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
uint32_t v___x_4163_; uint8_t v___x_4164_; 
v___x_4163_ = 5;
v___x_4164_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4155_, v___x_4163_);
if (v___x_4164_ == 0)
{
lean_object* v_lctx_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_lctx_4165_ = lean_ctor_get(v_a_4158_, 2);
v___x_4166_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4156_);
lean_inc_ref(v_lctx_4165_);
v___x_4167_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4165_, v___x_4166_, v_e_4155_, v_a_4156_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
return v___x_4167_;
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4168_ = lean_box(0);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v_e_4155_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec(v_a_4172_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
switch(lean_obj_tag(v_e_4180_))
{
case 0:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4188_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4189_ = l_Lean_MessageData_ofExpr(v_e_4180_);
v___x_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4188_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4190_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4191_;
}
case 1:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4180_, v___y_4183_, v___y_4185_, v___y_4186_);
return v___x_4192_;
}
case 2:
{
lean_object* v___x_4193_; 
v___x_4193_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4193_;
}
case 3:
{
lean_object* v_u_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_u_4194_ = lean_ctor_get(v_e_4180_, 0);
lean_inc(v_u_4194_);
v___x_4195_ = l_Lean_Level_succ___override(v_u_4194_);
v___x_4196_ = l_Lean_Expr_sort___override(v___x_4195_);
v___x_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_e_4180_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
case 4:
{
lean_object* v___x_4200_; 
v___x_4200_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4200_;
}
case 5:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
lean_inc_ref(v_e_4180_);
v___x_4201_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4201_, 0, v_e_4180_);
v___x_4202_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4180_, v___x_4201_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4202_;
}
case 7:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_inc_ref(v_e_4180_);
v___x_4203_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4203_, 0, v_e_4180_);
v___x_4204_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4180_, v___x_4203_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4204_;
}
case 9:
{
lean_object* v_a_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_a_4205_ = lean_ctor_get(v_e_4180_, 0);
v___x_4206_ = l_Lean_Literal_type(v_a_4205_);
v___x_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
v___x_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4208_, 0, v_e_4180_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
case 10:
{
lean_object* v_data_4210_; lean_object* v_expr_4211_; lean_object* v___x_4212_; 
v_data_4210_ = lean_ctor_get(v_e_4180_, 0);
v_expr_4211_ = lean_ctor_get(v_e_4180_, 1);
lean_inc_ref(v_expr_4211_);
v___x_4212_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4211_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4235_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4235_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4235_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v_expr_4217_; lean_object* v_type_x3f_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4234_; 
v_expr_4217_ = lean_ctor_get(v_a_4213_, 0);
v_type_x3f_4218_ = lean_ctor_get(v_a_4213_, 1);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_a_4213_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4220_ = v_a_4213_;
v_isShared_4221_ = v_isSharedCheck_4234_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_type_x3f_4218_);
lean_inc(v_expr_4217_);
lean_dec(v_a_4213_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4234_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___y_4223_; size_t v___x_4230_; size_t v___x_4231_; uint8_t v___x_4232_; 
v___x_4230_ = lean_ptr_addr(v_expr_4211_);
v___x_4231_ = lean_ptr_addr(v_expr_4217_);
v___x_4232_ = lean_usize_dec_eq(v___x_4230_, v___x_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; 
lean_inc(v_data_4210_);
lean_dec_ref_known(v_e_4180_, 2);
v___x_4233_ = l_Lean_Expr_mdata___override(v_data_4210_, v_expr_4217_);
v___y_4223_ = v___x_4233_;
goto v___jp_4222_;
}
else
{
lean_dec_ref(v_expr_4217_);
v___y_4223_ = v_e_4180_;
goto v___jp_4222_;
}
v___jp_4222_:
{
lean_object* v___x_4225_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___y_4223_);
v___x_4225_ = v___x_4220_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___y_4223_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_type_x3f_4218_);
v___x_4225_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
lean_object* v___x_4227_; 
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4225_);
v___x_4227_ = v___x_4215_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4180_, 2);
return v___x_4212_;
}
}
case 11:
{
lean_object* v_typeName_4236_; lean_object* v_idx_4237_; lean_object* v_struct_4238_; lean_object* v___f_4239_; lean_object* v___x_4240_; 
v_typeName_4236_ = lean_ctor_get(v_e_4180_, 0);
v_idx_4237_ = lean_ctor_get(v_e_4180_, 1);
v_struct_4238_ = lean_ctor_get(v_e_4180_, 2);
lean_inc(v_idx_4237_);
lean_inc(v_typeName_4236_);
lean_inc_ref(v_e_4180_);
lean_inc_ref(v_struct_4238_);
v___f_4239_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4239_, 0, v_struct_4238_);
lean_closure_set(v___f_4239_, 1, v_e_4180_);
lean_closure_set(v___f_4239_, 2, v_typeName_4236_);
lean_closure_set(v___f_4239_, 3, v_idx_4237_);
v___x_4240_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4180_, v___f_4239_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4240_;
}
default: 
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_inc_ref(v_e_4180_);
v___x_4241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4241_, 0, v_e_4180_);
v___x_4242_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4180_, v___x_4241_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4242_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4243_; double v___x_4244_; 
v___x_4243_ = lean_unsigned_to_nat(1000000000u);
v___x_4244_ = lean_float_of_nat(v___x_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v_toCold_4253_; lean_object* v_options_4254_; uint8_t v_hasTrace_4255_; 
v_toCold_4253_ = lean_ctor_get(v_a_4250_, 0);
v_options_4254_ = lean_ctor_get(v_toCold_4253_, 2);
v_hasTrace_4255_ = lean_ctor_get_uint8(v_options_4254_, sizeof(void*)*1);
if (v_hasTrace_4255_ == 0)
{
lean_object* v___x_4256_; 
v___x_4256_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
return v___x_4256_;
}
else
{
lean_object* v_inheritedTraceOptions_4257_; lean_object* v___f_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v_a_4266_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v_a_4281_; 
v_inheritedTraceOptions_4257_ = lean_ctor_get(v_toCold_4253_, 11);
lean_inc_ref(v_e_4245_);
v___f_4258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4258_, 0, v_e_4245_);
v___x_4259_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4260_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4261_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4257_, v_options_4254_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4339_ = l_Lean_trace_profiler;
v___x_4340_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4254_, v___x_4339_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4341_; 
lean_dec_ref(v___f_4258_);
v___x_4341_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
return v___x_4341_;
}
else
{
goto v___jp_4290_;
}
}
else
{
goto v___jp_4290_;
}
v___jp_4263_:
{
lean_object* v___x_4267_; double v___x_4268_; double v___x_4269_; double v___x_4270_; double v___x_4271_; double v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4267_ = lean_io_mono_nanos_now();
v___x_4268_ = lean_float_of_nat(v___y_4264_);
v___x_4269_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4270_ = lean_float_div(v___x_4268_, v___x_4269_);
v___x_4271_ = lean_float_of_nat(v___x_4267_);
v___x_4272_ = lean_float_div(v___x_4271_, v___x_4269_);
v___x_4273_ = lean_box_float(v___x_4270_);
v___x_4274_ = lean_box_float(v___x_4272_);
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4273_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4276_, 0, v_a_4266_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4259_, v_hasTrace_4255_, v___x_4260_, v_options_4254_, v___x_4262_, v___y_4265_, v___f_4258_, v___x_4276_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
return v___x_4277_;
}
v___jp_4278_:
{
lean_object* v___x_4282_; double v___x_4283_; double v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4282_ = lean_io_get_num_heartbeats();
v___x_4283_ = lean_float_of_nat(v___y_4279_);
v___x_4284_ = lean_float_of_nat(v___x_4282_);
v___x_4285_ = lean_box_float(v___x_4283_);
v___x_4286_ = lean_box_float(v___x_4284_);
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4288_, 0, v_a_4281_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
v___x_4289_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4259_, v_hasTrace_4255_, v___x_4260_, v_options_4254_, v___x_4262_, v___y_4280_, v___f_4258_, v___x_4288_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
return v___x_4289_;
}
v___jp_4290_:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4251_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4293_; uint8_t v___x_4294_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4294_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4254_, v___x_4293_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_io_mono_nanos_now();
v___x_4296_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 1);
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
v___y_4264_ = v___x_4295_;
v___y_4265_ = v_a_4292_;
v_a_4266_ = v___x_4302_;
goto v___jp_4263_;
}
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_a_4305_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4296_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4296_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set_tag(v___x_4307_, 0);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
v___y_4264_ = v___x_4295_;
v___y_4265_ = v_a_4292_;
v_a_4266_ = v___x_4310_;
goto v___jp_4263_;
}
}
}
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = lean_io_get_num_heartbeats();
v___x_4314_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
lean_ctor_set_tag(v___x_4317_, 1);
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
v___y_4279_ = v___x_4313_;
v___y_4280_ = v_a_4292_;
v_a_4281_ = v___x_4320_;
goto v___jp_4278_;
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_a_4323_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4314_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4314_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set_tag(v___x_4325_, 0);
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
v___y_4279_ = v___x_4313_;
v___y_4280_ = v_a_4292_;
v_a_4281_ = v___x_4328_;
goto v___jp_4278_;
}
}
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec_ref(v___f_4258_);
lean_dec_ref(v_e_4245_);
v_a_4331_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4291_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4291_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4342_, lean_object* v_e_4343_, lean_object* v_typeName_4344_, lean_object* v_idx_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4342_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4343_, v_typeName_4344_, v_idx_4345_, v_a_4354_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
return v___x_4355_;
}
else
{
lean_dec(v_idx_4345_);
lean_dec(v_typeName_4344_);
lean_dec_ref(v_e_4343_);
return v___x_4353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_);
lean_dec(v_a_4362_);
lean_dec_ref(v_a_4361_);
lean_dec(v_a_4360_);
lean_dec_ref(v_a_4359_);
lean_dec(v_a_4358_);
lean_dec(v_a_4357_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4365_, lean_object* v_fvars_4366_, lean_object* v_doms_4367_, lean_object* v_e_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4365_, v_fvars_4366_, v_doms_4367_, v_e_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_a_4370_);
lean_dec(v_a_4369_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec(v___y_4379_);
lean_dec(v___y_4378_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4386_, lean_object* v_fvars_4387_, lean_object* v_e_4388_, lean_object* v_letFVars_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4386_, v_fvars_4387_, v_e_4388_, v_letFVars_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
lean_dec(v_a_4395_);
lean_dec_ref(v_a_4394_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec(v_a_4390_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4398_, lean_object* v_lctx_4399_, lean_object* v_localInsts_4400_, lean_object* v_x_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4399_, v_localInsts_4400_, v_x_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4410_, lean_object* v_lctx_4411_, lean_object* v_localInsts_4412_, lean_object* v_x_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4410_, v_lctx_4411_, v_localInsts_4412_, v_x_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4415_);
lean_dec(v___y_4414_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4422_, lean_object* v_lctx_4423_, lean_object* v_x_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4423_, v_x_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4433_, lean_object* v_lctx_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4433_, v_lctx_4434_, v_x_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec(v___y_4436_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4449_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec(v___y_4452_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v___x_4467_; 
v___x_4467_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4465_);
return v___x_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec(v___y_4468_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4476_, lean_object* v_x_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4477_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4486_, lean_object* v_x_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4486_, v_x_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec(v___y_4488_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4496_, lean_object* v_data_4497_, lean_object* v_ref_4498_, lean_object* v_msg_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4496_, v_data_4497_, v_ref_4498_, v_msg_4499_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4508_, lean_object* v_data_4509_, lean_object* v_ref_4510_, lean_object* v_msg_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4508_, v_data_4509_, v_ref_4510_, v_msg_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec(v___y_4512_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v_traceState_4523_; lean_object* v_traces_4524_; lean_object* v___x_4525_; lean_object* v_traceState_4526_; lean_object* v_env_4527_; lean_object* v_nextMacroScope_4528_; lean_object* v_ngen_4529_; lean_object* v_auxDeclNGen_4530_; lean_object* v_cache_4531_; lean_object* v_recordedDeps_4532_; lean_object* v_messages_4533_; lean_object* v_infoState_4534_; lean_object* v_snapshotTasks_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4556_; 
v___x_4522_ = lean_st_ref_get(v___y_4520_);
v_traceState_4523_ = lean_ctor_get(v___x_4522_, 4);
lean_inc_ref(v_traceState_4523_);
lean_dec(v___x_4522_);
v_traces_4524_ = lean_ctor_get(v_traceState_4523_, 0);
lean_inc_ref(v_traces_4524_);
lean_dec_ref(v_traceState_4523_);
v___x_4525_ = lean_st_ref_take(v___y_4520_);
v_traceState_4526_ = lean_ctor_get(v___x_4525_, 4);
v_env_4527_ = lean_ctor_get(v___x_4525_, 0);
v_nextMacroScope_4528_ = lean_ctor_get(v___x_4525_, 1);
v_ngen_4529_ = lean_ctor_get(v___x_4525_, 2);
v_auxDeclNGen_4530_ = lean_ctor_get(v___x_4525_, 3);
v_cache_4531_ = lean_ctor_get(v___x_4525_, 5);
v_recordedDeps_4532_ = lean_ctor_get(v___x_4525_, 6);
v_messages_4533_ = lean_ctor_get(v___x_4525_, 7);
v_infoState_4534_ = lean_ctor_get(v___x_4525_, 8);
v_snapshotTasks_4535_ = lean_ctor_get(v___x_4525_, 9);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4537_ = v___x_4525_;
v_isShared_4538_ = v_isSharedCheck_4556_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_snapshotTasks_4535_);
lean_inc(v_infoState_4534_);
lean_inc(v_messages_4533_);
lean_inc(v_recordedDeps_4532_);
lean_inc(v_cache_4531_);
lean_inc(v_traceState_4526_);
lean_inc(v_auxDeclNGen_4530_);
lean_inc(v_ngen_4529_);
lean_inc(v_nextMacroScope_4528_);
lean_inc(v_env_4527_);
lean_dec(v___x_4525_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4556_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
uint64_t v_tid_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4554_; 
v_tid_4539_ = lean_ctor_get_uint64(v_traceState_4526_, sizeof(void*)*1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_traceState_4526_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v_traceState_4526_, 0);
lean_dec(v_unused_4555_);
v___x_4541_ = v_traceState_4526_;
v_isShared_4542_ = v_isSharedCheck_4554_;
goto v_resetjp_4540_;
}
else
{
lean_dec(v_traceState_4526_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4554_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4547_; 
v___x_4543_ = lean_unsigned_to_nat(32u);
v___x_4544_ = lean_mk_empty_array_with_capacity(v___x_4543_);
lean_dec_ref(v___x_4544_);
v___x_4545_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4545_);
v___x_4547_ = v___x_4541_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4545_);
lean_ctor_set_uint64(v_reuseFailAlloc_4553_, sizeof(void*)*1, v_tid_4539_);
v___x_4547_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
lean_object* v___x_4549_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 4, v___x_4547_);
v___x_4549_ = v___x_4537_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_env_4527_);
lean_ctor_set(v_reuseFailAlloc_4552_, 1, v_nextMacroScope_4528_);
lean_ctor_set(v_reuseFailAlloc_4552_, 2, v_ngen_4529_);
lean_ctor_set(v_reuseFailAlloc_4552_, 3, v_auxDeclNGen_4530_);
lean_ctor_set(v_reuseFailAlloc_4552_, 4, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4552_, 5, v_cache_4531_);
lean_ctor_set(v_reuseFailAlloc_4552_, 6, v_recordedDeps_4532_);
lean_ctor_set(v_reuseFailAlloc_4552_, 7, v_messages_4533_);
lean_ctor_set(v_reuseFailAlloc_4552_, 8, v_infoState_4534_);
lean_ctor_set(v_reuseFailAlloc_4552_, 9, v_snapshotTasks_4535_);
v___x_4549_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4550_ = lean_st_ref_put(v___y_4520_, v___x_4549_);
v___x_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4551_, 0, v_traces_4524_);
return v___x_4551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4557_);
lean_dec(v___y_4557_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4563_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4572_, lean_object* v_msg_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_ref_4579_; lean_object* v___x_4580_; lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4626_; 
v_ref_4579_ = lean_ctor_get(v___y_4576_, 2);
v___x_4580_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4626_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4626_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v_traceState_4586_; lean_object* v_env_4587_; lean_object* v_nextMacroScope_4588_; lean_object* v_ngen_4589_; lean_object* v_auxDeclNGen_4590_; lean_object* v_cache_4591_; lean_object* v_recordedDeps_4592_; lean_object* v_messages_4593_; lean_object* v_infoState_4594_; lean_object* v_snapshotTasks_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4625_; 
v___x_4585_ = lean_st_ref_take(v___y_4577_);
v_traceState_4586_ = lean_ctor_get(v___x_4585_, 4);
v_env_4587_ = lean_ctor_get(v___x_4585_, 0);
v_nextMacroScope_4588_ = lean_ctor_get(v___x_4585_, 1);
v_ngen_4589_ = lean_ctor_get(v___x_4585_, 2);
v_auxDeclNGen_4590_ = lean_ctor_get(v___x_4585_, 3);
v_cache_4591_ = lean_ctor_get(v___x_4585_, 5);
v_recordedDeps_4592_ = lean_ctor_get(v___x_4585_, 6);
v_messages_4593_ = lean_ctor_get(v___x_4585_, 7);
v_infoState_4594_ = lean_ctor_get(v___x_4585_, 8);
v_snapshotTasks_4595_ = lean_ctor_get(v___x_4585_, 9);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4597_ = v___x_4585_;
v_isShared_4598_ = v_isSharedCheck_4625_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_snapshotTasks_4595_);
lean_inc(v_infoState_4594_);
lean_inc(v_messages_4593_);
lean_inc(v_recordedDeps_4592_);
lean_inc(v_cache_4591_);
lean_inc(v_traceState_4586_);
lean_inc(v_auxDeclNGen_4590_);
lean_inc(v_ngen_4589_);
lean_inc(v_nextMacroScope_4588_);
lean_inc(v_env_4587_);
lean_dec(v___x_4585_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4625_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
uint64_t v_tid_4599_; lean_object* v_traces_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4624_; 
v_tid_4599_ = lean_ctor_get_uint64(v_traceState_4586_, sizeof(void*)*1);
v_traces_4600_ = lean_ctor_get(v_traceState_4586_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_traceState_4586_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4602_ = v_traceState_4586_;
v_isShared_4603_ = v_isSharedCheck_4624_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_traces_4600_);
lean_dec(v_traceState_4586_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4624_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; double v___x_4606_; uint8_t v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4604_ = lean_box(0);
v___x_4605_ = lean_box(0);
v___x_4606_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4607_ = 0;
v___x_4608_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4609_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4609_, 0, v_cls_4572_);
lean_ctor_set(v___x_4609_, 1, v___x_4605_);
lean_ctor_set(v___x_4609_, 2, v___x_4608_);
lean_ctor_set_float(v___x_4609_, sizeof(void*)*3, v___x_4606_);
lean_ctor_set_float(v___x_4609_, sizeof(void*)*3 + 8, v___x_4606_);
lean_ctor_set_uint8(v___x_4609_, sizeof(void*)*3 + 16, v___x_4607_);
v___x_4610_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4611_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4609_);
lean_ctor_set(v___x_4611_, 1, v_a_4581_);
lean_ctor_set(v___x_4611_, 2, v___x_4610_);
lean_inc(v_ref_4579_);
v___x_4612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4612_, 0, v_ref_4579_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
v___x_4613_ = l_Lean_PersistentArray_push___redArg(v_traces_4600_, v___x_4612_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4613_);
v___x_4615_ = v___x_4602_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4613_);
lean_ctor_set_uint64(v_reuseFailAlloc_4623_, sizeof(void*)*1, v_tid_4599_);
v___x_4615_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4617_; 
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 4, v___x_4615_);
v___x_4617_ = v___x_4597_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_env_4587_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_nextMacroScope_4588_);
lean_ctor_set(v_reuseFailAlloc_4622_, 2, v_ngen_4589_);
lean_ctor_set(v_reuseFailAlloc_4622_, 3, v_auxDeclNGen_4590_);
lean_ctor_set(v_reuseFailAlloc_4622_, 4, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4622_, 5, v_cache_4591_);
lean_ctor_set(v_reuseFailAlloc_4622_, 6, v_recordedDeps_4592_);
lean_ctor_set(v_reuseFailAlloc_4622_, 7, v_messages_4593_);
lean_ctor_set(v_reuseFailAlloc_4622_, 8, v_infoState_4594_);
lean_ctor_set(v_reuseFailAlloc_4622_, 9, v_snapshotTasks_4595_);
v___x_4617_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4618_ = lean_st_ref_put(v___y_4577_, v___x_4617_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4604_);
v___x_4620_ = v___x_4583_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4604_);
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
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0));
v___x_4637_ = l_Lean_stringToMessageData(v___x_4636_);
return v___x_4637_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2));
v___x_4640_ = l_Lean_stringToMessageData(v___x_4639_);
return v___x_4640_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4642_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4));
v___x_4643_ = l_Lean_stringToMessageData(v___x_4642_);
return v___x_4643_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6));
v___x_4646_ = l_Lean_stringToMessageData(v___x_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___x_4647_, lean_object* v_e_4648_, lean_object* v___x_4649_, lean_object* v___x_4650_, lean_object* v_cls_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_st_mk_ref(v___x_4647_);
v___x_4658_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4648_, v___x_4649_, v___x_4657_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4730_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4730_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4730_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4663_; lean_object* v_count_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4728_; 
v___x_4663_ = lean_st_ref_get(v___x_4657_);
lean_dec(v___x_4657_);
v_count_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4728_ == 0)
{
lean_object* v_unused_4729_; 
v_unused_4729_ = lean_ctor_get(v___x_4663_, 1);
lean_dec(v_unused_4729_);
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4728_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_count_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4728_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
uint8_t v___x_4690_; 
v___x_4690_ = lean_nat_dec_eq(v_count_4664_, v___x_4650_);
if (v___x_4690_ == 0)
{
lean_object* v_toCold_4691_; lean_object* v_options_4692_; uint8_t v_hasTrace_4693_; 
v_toCold_4691_ = lean_ctor_get(v___y_4654_, 0);
v_options_4692_ = lean_ctor_get(v_toCold_4691_, 2);
v_hasTrace_4693_ = lean_ctor_get_uint8(v_options_4692_, sizeof(void*)*1);
if (v_hasTrace_4693_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v_inheritedTraceOptions_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; uint8_t v___x_4697_; 
v_inheritedTraceOptions_4694_ = lean_ctor_get(v_toCold_4691_, 11);
v___x_4695_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4651_);
v___x_4696_ = l_Lean_Name_append(v___x_4695_, v_cls_4651_);
v___x_4697_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4694_, v_options_4692_, v___x_4696_);
lean_dec(v___x_4696_);
if (v___x_4697_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v_expr_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v_expr_4698_ = lean_ctor_get(v_a_4659_, 0);
v___x_4699_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5);
lean_inc_ref(v_expr_4698_);
v___x_4700_ = l_Lean_indentExpr(v_expr_4698_);
v___x_4701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4701_, 0, v___x_4699_);
lean_ctor_set(v___x_4701_, 1, v___x_4700_);
v___x_4702_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4651_, v___x_4701_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_dec_ref_known(v___x_4702_, 1);
goto v___jp_4668_;
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_del_object(v___x_4666_);
lean_dec(v_count_4664_);
lean_del_object(v___x_4661_);
lean_dec(v_a_4659_);
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4702_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4702_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4711_; lean_object* v_options_4712_; uint8_t v_hasTrace_4713_; 
v_toCold_4711_ = lean_ctor_get(v___y_4654_, 0);
v_options_4712_ = lean_ctor_get(v_toCold_4711_, 2);
v_hasTrace_4713_ = lean_ctor_get_uint8(v_options_4712_, sizeof(void*)*1);
if (v_hasTrace_4713_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v_inheritedTraceOptions_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; 
v_inheritedTraceOptions_4714_ = lean_ctor_get(v_toCold_4711_, 11);
v___x_4715_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4651_);
v___x_4716_ = l_Lean_Name_append(v___x_4715_, v_cls_4651_);
v___x_4717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4714_, v_options_4712_, v___x_4716_);
lean_dec(v___x_4716_);
if (v___x_4717_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7);
v___x_4719_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4651_, v___x_4718_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_dec_ref_known(v___x_4719_, 1);
goto v___jp_4668_;
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_del_object(v___x_4666_);
lean_dec(v_count_4664_);
lean_del_object(v___x_4661_);
lean_dec(v_a_4659_);
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4719_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4719_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
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
v___x_4673_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1);
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
v___x_4679_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3);
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
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
lean_dec(v___x_4657_);
lean_dec(v_cls_4651_);
v_a_4731_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4658_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4658_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___x_4739_, lean_object* v_e_4740_, lean_object* v___x_4741_, lean_object* v___x_4742_, lean_object* v_cls_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___x_4739_, v_e_4740_, v___x_4741_, v___x_4742_, v_cls_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___x_4742_);
lean_dec(v___x_4741_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(uint8_t v___x_4750_, lean_object* v___f_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
lean_object* v___x_4802_; uint8_t v_beta_4803_; 
v___x_4802_ = l_Lean_Meta_Context_config(v___y_4752_);
v_beta_4803_ = lean_ctor_get_uint8(v___x_4802_, 13);
if (v_beta_4803_ == 0)
{
lean_dec_ref(v___x_4802_);
goto v___jp_4757_;
}
else
{
uint8_t v_iota_4804_; 
v_iota_4804_ = lean_ctor_get_uint8(v___x_4802_, 12);
if (v_iota_4804_ == 0)
{
lean_dec_ref(v___x_4802_);
goto v___jp_4757_;
}
else
{
uint8_t v_zeta_4805_; 
v_zeta_4805_ = lean_ctor_get_uint8(v___x_4802_, 15);
if (v_zeta_4805_ == 0)
{
lean_dec_ref(v___x_4802_);
goto v___jp_4757_;
}
else
{
uint8_t v_zetaHave_4806_; 
v_zetaHave_4806_ = lean_ctor_get_uint8(v___x_4802_, 18);
if (v_zetaHave_4806_ == 0)
{
lean_dec_ref(v___x_4802_);
goto v___jp_4757_;
}
else
{
uint8_t v_zetaDelta_4807_; 
v_zetaDelta_4807_ = lean_ctor_get_uint8(v___x_4802_, 16);
if (v_zetaDelta_4807_ == 0)
{
lean_dec_ref(v___x_4802_);
goto v___jp_4757_;
}
else
{
uint8_t v_etaStruct_4808_; uint8_t v_proj_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; 
v_etaStruct_4808_ = lean_ctor_get_uint8(v___x_4802_, 10);
v_proj_4809_ = lean_ctor_get_uint8(v___x_4802_, 14);
lean_dec_ref(v___x_4802_);
v___x_4810_ = lean_box(v_proj_4809_);
v___x_4811_ = lean_obj_tag_nat(v___x_4810_);
lean_dec(v___x_4810_);
v___x_4812_ = lean_unsigned_to_nat(2u);
v___x_4813_ = lean_nat_dec_eq(v___x_4811_, v___x_4812_);
if (v___x_4813_ == 0)
{
goto v___jp_4757_;
}
else
{
uint8_t v___x_4814_; uint8_t v___x_4815_; 
v___x_4814_ = 0;
v___x_4815_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4808_, v___x_4814_);
if (v___x_4815_ == 0)
{
goto v___jp_4757_;
}
else
{
lean_object* v___x_4816_; 
v___x_4816_ = lean_apply_5(v___f_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, lean_box(0));
return v___x_4816_;
}
}
}
}
}
}
}
v___jp_4757_:
{
lean_object* v___x_4758_; uint8_t v_foApprox_4759_; uint8_t v_ctxApprox_4760_; uint8_t v_quasiPatternApprox_4761_; uint8_t v_constApprox_4762_; uint8_t v_isDefEqStuckEx_4763_; uint8_t v_unificationHints_4764_; uint8_t v_proofIrrelevance_4765_; uint8_t v_assignSyntheticOpaque_4766_; uint8_t v_offsetCnstrs_4767_; uint8_t v_transparency_4768_; uint8_t v_univApprox_4769_; uint8_t v_zetaUnused_4770_; uint8_t v_canUnfoldPredicateConfig_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4801_; 
v___x_4758_ = l_Lean_Meta_Context_config(v___y_4752_);
v_foApprox_4759_ = lean_ctor_get_uint8(v___x_4758_, 0);
v_ctxApprox_4760_ = lean_ctor_get_uint8(v___x_4758_, 1);
v_quasiPatternApprox_4761_ = lean_ctor_get_uint8(v___x_4758_, 2);
v_constApprox_4762_ = lean_ctor_get_uint8(v___x_4758_, 3);
v_isDefEqStuckEx_4763_ = lean_ctor_get_uint8(v___x_4758_, 4);
v_unificationHints_4764_ = lean_ctor_get_uint8(v___x_4758_, 5);
v_proofIrrelevance_4765_ = lean_ctor_get_uint8(v___x_4758_, 6);
v_assignSyntheticOpaque_4766_ = lean_ctor_get_uint8(v___x_4758_, 7);
v_offsetCnstrs_4767_ = lean_ctor_get_uint8(v___x_4758_, 8);
v_transparency_4768_ = lean_ctor_get_uint8(v___x_4758_, 9);
v_univApprox_4769_ = lean_ctor_get_uint8(v___x_4758_, 11);
v_zetaUnused_4770_ = lean_ctor_get_uint8(v___x_4758_, 17);
v_canUnfoldPredicateConfig_4771_ = lean_ctor_get_uint8(v___x_4758_, 19);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4773_ = v___x_4758_;
v_isShared_4774_ = v_isSharedCheck_4801_;
goto v_resetjp_4772_;
}
else
{
lean_dec(v___x_4758_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4801_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
uint8_t v___x_4775_; uint8_t v___x_4776_; lean_object* v___x_4778_; 
v___x_4775_ = 0;
v___x_4776_ = 2;
if (v_isShared_4774_ == 0)
{
v___x_4778_ = v___x_4773_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 0, v_foApprox_4759_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 1, v_ctxApprox_4760_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 2, v_quasiPatternApprox_4761_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 3, v_constApprox_4762_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 4, v_isDefEqStuckEx_4763_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 5, v_unificationHints_4764_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 6, v_proofIrrelevance_4765_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 7, v_assignSyntheticOpaque_4766_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 8, v_offsetCnstrs_4767_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 9, v_transparency_4768_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 11, v_univApprox_4769_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 17, v_zetaUnused_4770_);
lean_ctor_set_uint8(v_reuseFailAlloc_4800_, 19, v_canUnfoldPredicateConfig_4771_);
v___x_4778_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
uint8_t v_trackZetaDelta_4779_; lean_object* v_zetaDeltaSet_4780_; lean_object* v_lctx_4781_; lean_object* v_localInstances_4782_; lean_object* v_defEqCtx_x3f_4783_; lean_object* v_synthPendingDepth_4784_; lean_object* v_customCanUnfoldPredicate_x3f_4785_; uint8_t v_univApprox_4786_; uint8_t v_inTypeClassResolution_4787_; uint8_t v_cacheInferType_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4798_; 
lean_ctor_set_uint8(v___x_4778_, 10, v___x_4775_);
lean_ctor_set_uint8(v___x_4778_, 12, v___x_4750_);
lean_ctor_set_uint8(v___x_4778_, 13, v___x_4750_);
lean_ctor_set_uint8(v___x_4778_, 14, v___x_4776_);
lean_ctor_set_uint8(v___x_4778_, 15, v___x_4750_);
lean_ctor_set_uint8(v___x_4778_, 16, v___x_4750_);
lean_ctor_set_uint8(v___x_4778_, 18, v___x_4750_);
v_trackZetaDelta_4779_ = lean_ctor_get_uint8(v___y_4752_, sizeof(void*)*7);
v_zetaDeltaSet_4780_ = lean_ctor_get(v___y_4752_, 1);
v_lctx_4781_ = lean_ctor_get(v___y_4752_, 2);
v_localInstances_4782_ = lean_ctor_get(v___y_4752_, 3);
v_defEqCtx_x3f_4783_ = lean_ctor_get(v___y_4752_, 4);
v_synthPendingDepth_4784_ = lean_ctor_get(v___y_4752_, 5);
v_customCanUnfoldPredicate_x3f_4785_ = lean_ctor_get(v___y_4752_, 6);
v_univApprox_4786_ = lean_ctor_get_uint8(v___y_4752_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4787_ = lean_ctor_get_uint8(v___y_4752_, sizeof(void*)*7 + 2);
v_cacheInferType_4788_ = lean_ctor_get_uint8(v___y_4752_, sizeof(void*)*7 + 3);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___y_4752_);
if (v_isSharedCheck_4798_ == 0)
{
lean_object* v_unused_4799_; 
v_unused_4799_ = lean_ctor_get(v___y_4752_, 0);
lean_dec(v_unused_4799_);
v___x_4790_ = v___y_4752_;
v_isShared_4791_ = v_isSharedCheck_4798_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4785_);
lean_inc(v_synthPendingDepth_4784_);
lean_inc(v_defEqCtx_x3f_4783_);
lean_inc(v_localInstances_4782_);
lean_inc(v_lctx_4781_);
lean_inc(v_zetaDeltaSet_4780_);
lean_dec(v___y_4752_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4798_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
uint64_t v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4795_; 
v___x_4792_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4778_);
v___x_4793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4793_, 0, v___x_4778_);
lean_ctor_set_uint64(v___x_4793_, sizeof(void*)*1, v___x_4792_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4793_);
v___x_4795_ = v___x_4790_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4793_);
lean_ctor_set(v_reuseFailAlloc_4797_, 1, v_zetaDeltaSet_4780_);
lean_ctor_set(v_reuseFailAlloc_4797_, 2, v_lctx_4781_);
lean_ctor_set(v_reuseFailAlloc_4797_, 3, v_localInstances_4782_);
lean_ctor_set(v_reuseFailAlloc_4797_, 4, v_defEqCtx_x3f_4783_);
lean_ctor_set(v_reuseFailAlloc_4797_, 5, v_synthPendingDepth_4784_);
lean_ctor_set(v_reuseFailAlloc_4797_, 6, v_customCanUnfoldPredicate_x3f_4785_);
lean_ctor_set_uint8(v_reuseFailAlloc_4797_, sizeof(void*)*7, v_trackZetaDelta_4779_);
lean_ctor_set_uint8(v_reuseFailAlloc_4797_, sizeof(void*)*7 + 1, v_univApprox_4786_);
lean_ctor_set_uint8(v_reuseFailAlloc_4797_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4787_);
lean_ctor_set_uint8(v_reuseFailAlloc_4797_, sizeof(void*)*7 + 3, v_cacheInferType_4788_);
v___x_4795_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
lean_object* v___x_4796_; 
v___x_4796_ = lean_apply_5(v___f_4751_, v___x_4795_, v___y_4753_, v___y_4754_, v___y_4755_, lean_box(0));
return v___x_4796_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4817_, lean_object* v___f_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
uint8_t v___x_14044__boxed_4824_; lean_object* v_res_4825_; 
v___x_14044__boxed_4824_ = lean_unbox(v___x_4817_);
v_res_4825_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_14044__boxed_4824_, v___f_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4826_, lean_object* v_cache_4827_, lean_object* v_a_x3f_4828_){
_start:
{
lean_object* v___x_4830_; lean_object* v_mctx_4831_; lean_object* v_zetaDeltaFVarIds_4832_; lean_object* v_postponed_4833_; lean_object* v_diag_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4844_; 
v___x_4830_ = lean_st_ref_take(v___y_4826_);
v_mctx_4831_ = lean_ctor_get(v___x_4830_, 0);
v_zetaDeltaFVarIds_4832_ = lean_ctor_get(v___x_4830_, 2);
v_postponed_4833_ = lean_ctor_get(v___x_4830_, 3);
v_diag_4834_ = lean_ctor_get(v___x_4830_, 4);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4844_ == 0)
{
lean_object* v_unused_4845_; 
v_unused_4845_ = lean_ctor_get(v___x_4830_, 1);
lean_dec(v_unused_4845_);
v___x_4836_ = v___x_4830_;
v_isShared_4837_ = v_isSharedCheck_4844_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_diag_4834_);
lean_inc(v_postponed_4833_);
lean_inc(v_zetaDeltaFVarIds_4832_);
lean_inc(v_mctx_4831_);
lean_dec(v___x_4830_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4844_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4838_ = lean_box(0);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v_cache_4827_);
v___x_4840_ = v___x_4836_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_mctx_4831_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v_cache_4827_);
lean_ctor_set(v_reuseFailAlloc_4843_, 2, v_zetaDeltaFVarIds_4832_);
lean_ctor_set(v_reuseFailAlloc_4843_, 3, v_postponed_4833_);
lean_ctor_set(v_reuseFailAlloc_4843_, 4, v_diag_4834_);
v___x_4840_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = lean_st_ref_put(v___y_4826_, v___x_4840_);
v___x_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4838_);
return v___x_4842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4846_, lean_object* v_cache_4847_, lean_object* v_a_x3f_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4846_, v_cache_4847_, v_a_x3f_4848_);
lean_dec(v_a_x3f_4848_);
lean_dec(v___y_4846_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(lean_object* v___y_4851_, lean_object* v_zetaDeltaFVarIds_4852_, lean_object* v_a_x3f_4853_){
_start:
{
lean_object* v___x_4855_; lean_object* v_mctx_4856_; lean_object* v_cache_4857_; lean_object* v_postponed_4858_; lean_object* v_diag_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4869_; 
v___x_4855_ = lean_st_ref_take(v___y_4851_);
v_mctx_4856_ = lean_ctor_get(v___x_4855_, 0);
v_cache_4857_ = lean_ctor_get(v___x_4855_, 1);
v_postponed_4858_ = lean_ctor_get(v___x_4855_, 3);
v_diag_4859_ = lean_ctor_get(v___x_4855_, 4);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4869_ == 0)
{
lean_object* v_unused_4870_; 
v_unused_4870_ = lean_ctor_get(v___x_4855_, 2);
lean_dec(v_unused_4870_);
v___x_4861_ = v___x_4855_;
v_isShared_4862_ = v_isSharedCheck_4869_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_diag_4859_);
lean_inc(v_postponed_4858_);
lean_inc(v_cache_4857_);
lean_inc(v_mctx_4856_);
lean_dec(v___x_4855_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4869_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4863_ = lean_box(0);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 2, v_zetaDeltaFVarIds_4852_);
v___x_4865_ = v___x_4861_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_mctx_4856_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v_cache_4857_);
lean_ctor_set(v_reuseFailAlloc_4868_, 2, v_zetaDeltaFVarIds_4852_);
lean_ctor_set(v_reuseFailAlloc_4868_, 3, v_postponed_4858_);
lean_ctor_set(v_reuseFailAlloc_4868_, 4, v_diag_4859_);
v___x_4865_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4866_ = lean_st_ref_put(v___y_4851_, v___x_4865_);
v___x_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4863_);
return v___x_4867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___y_4871_, lean_object* v_zetaDeltaFVarIds_4872_, lean_object* v_a_x3f_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4871_, v_zetaDeltaFVarIds_4872_, v_a_x3f_4873_);
lean_dec(v_a_x3f_4873_);
lean_dec(v___y_4871_);
return v_res_4875_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1));
v___x_4880_ = l_Lean_MessageData_ofFormat(v___x_4879_);
return v___x_4880_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4881_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4882_ = lean_unsigned_to_nat(0u);
v___x_4883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
lean_ctor_set(v___x_4883_, 1, v___x_4881_);
return v___x_4883_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4884_);
return v___x_4885_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4886_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4887_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
lean_ctor_set(v___x_4887_, 2, v___x_4886_);
lean_ctor_set(v___x_4887_, 3, v___x_4886_);
lean_ctor_set(v___x_4887_, 4, v___x_4886_);
lean_ctor_set(v___x_4887_, 5, v___x_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_4888_, lean_object* v_e_4889_, lean_object* v_cls_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
if (v___x_4888_ == 0)
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
lean_dec(v_cls_4890_);
v___x_4896_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_4897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4897_, 0, v_e_4889_);
lean_ctor_set(v___x_4897_, 1, v___x_4896_);
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
return v___x_4898_;
}
else
{
uint8_t v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___f_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v_cache_4906_; lean_object* v_a_4908_; lean_object* v___x_4919_; lean_object* v_mctx_4920_; lean_object* v_zetaDeltaFVarIds_4921_; lean_object* v_postponed_4922_; lean_object* v_diag_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_5001_; 
v___x_4899_ = 0;
v___x_4900_ = lean_box(0);
v___x_4901_ = lean_unsigned_to_nat(0u);
v___x_4902_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___f_4903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4903_, 0, v___x_4902_);
lean_closure_set(v___f_4903_, 1, v_e_4889_);
lean_closure_set(v___f_4903_, 2, v___x_4900_);
lean_closure_set(v___f_4903_, 3, v___x_4901_);
lean_closure_set(v___f_4903_, 4, v_cls_4890_);
v___x_4904_ = lean_box(1);
v___x_4905_ = lean_st_ref_get(v___y_4892_);
v_cache_4906_ = lean_ctor_get(v___x_4905_, 1);
lean_inc_ref(v_cache_4906_);
lean_dec(v___x_4905_);
v___x_4919_ = lean_st_ref_take(v___y_4892_);
v_mctx_4920_ = lean_ctor_get(v___x_4919_, 0);
v_zetaDeltaFVarIds_4921_ = lean_ctor_get(v___x_4919_, 2);
v_postponed_4922_ = lean_ctor_get(v___x_4919_, 3);
v_diag_4923_ = lean_ctor_get(v___x_4919_, 4);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_5001_ == 0)
{
lean_object* v_unused_5002_; 
v_unused_5002_ = lean_ctor_get(v___x_4919_, 1);
lean_dec(v_unused_5002_);
v___x_4925_ = v___x_4919_;
v_isShared_4926_ = v_isSharedCheck_5001_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_diag_4923_);
lean_inc(v_postponed_4922_);
lean_inc(v_zetaDeltaFVarIds_4921_);
lean_inc(v_mctx_4920_);
lean_dec(v___x_4919_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_5001_;
goto v_resetjp_4924_;
}
v___jp_4907_:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
v___x_4909_ = lean_box(0);
v___x_4910_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4892_, v_cache_4906_, v___x_4909_);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4917_ == 0)
{
lean_object* v_unused_4918_; 
v_unused_4918_ = lean_ctor_get(v___x_4910_, 0);
lean_dec(v_unused_4918_);
v___x_4912_ = v___x_4910_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_dec(v___x_4910_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
lean_ctor_set_tag(v___x_4912_, 1);
lean_ctor_set(v___x_4912_, 0, v_a_4908_);
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4908_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; lean_object* v___x_4929_; 
v___x_4927_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 1, v___x_4927_);
v___x_4929_ = v___x_4925_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_mctx_4920_);
lean_ctor_set(v_reuseFailAlloc_5000_, 1, v___x_4927_);
lean_ctor_set(v_reuseFailAlloc_5000_, 2, v_zetaDeltaFVarIds_4921_);
lean_ctor_set(v_reuseFailAlloc_5000_, 3, v_postponed_4922_);
lean_ctor_set(v_reuseFailAlloc_5000_, 4, v_diag_4923_);
v___x_4929_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4930_; lean_object* v_keyedConfig_4931_; lean_object* v_zetaDeltaSet_4932_; lean_object* v_lctx_4933_; lean_object* v_localInstances_4934_; lean_object* v_defEqCtx_x3f_4935_; lean_object* v_synthPendingDepth_4936_; lean_object* v_customCanUnfoldPredicate_x3f_4937_; uint8_t v_univApprox_4938_; uint8_t v_inTypeClassResolution_4939_; uint8_t v_cacheInferType_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v_mctx_4943_; lean_object* v_cache_4944_; lean_object* v_zetaDeltaFVarIds_4945_; lean_object* v_postponed_4946_; lean_object* v_diag_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4999_; 
v___x_4930_ = lean_st_ref_put(v___y_4892_, v___x_4929_);
v_keyedConfig_4931_ = lean_ctor_get(v___y_4891_, 0);
v_zetaDeltaSet_4932_ = lean_ctor_get(v___y_4891_, 1);
v_lctx_4933_ = lean_ctor_get(v___y_4891_, 2);
v_localInstances_4934_ = lean_ctor_get(v___y_4891_, 3);
v_defEqCtx_x3f_4935_ = lean_ctor_get(v___y_4891_, 4);
v_synthPendingDepth_4936_ = lean_ctor_get(v___y_4891_, 5);
v_customCanUnfoldPredicate_x3f_4937_ = lean_ctor_get(v___y_4891_, 6);
v_univApprox_4938_ = lean_ctor_get_uint8(v___y_4891_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4939_ = lean_ctor_get_uint8(v___y_4891_, sizeof(void*)*7 + 2);
v_cacheInferType_4940_ = lean_ctor_get_uint8(v___y_4891_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_4937_);
lean_inc(v_synthPendingDepth_4936_);
lean_inc(v_defEqCtx_x3f_4935_);
lean_inc_ref(v_localInstances_4934_);
lean_inc_ref(v_lctx_4933_);
lean_inc(v_zetaDeltaSet_4932_);
lean_inc_ref(v_keyedConfig_4931_);
v___x_4941_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4941_, 0, v_keyedConfig_4931_);
lean_ctor_set(v___x_4941_, 1, v_zetaDeltaSet_4932_);
lean_ctor_set(v___x_4941_, 2, v_lctx_4933_);
lean_ctor_set(v___x_4941_, 3, v_localInstances_4934_);
lean_ctor_set(v___x_4941_, 4, v_defEqCtx_x3f_4935_);
lean_ctor_set(v___x_4941_, 5, v_synthPendingDepth_4936_);
lean_ctor_set(v___x_4941_, 6, v_customCanUnfoldPredicate_x3f_4937_);
lean_ctor_set_uint8(v___x_4941_, sizeof(void*)*7, v___x_4888_);
lean_ctor_set_uint8(v___x_4941_, sizeof(void*)*7 + 1, v_univApprox_4938_);
lean_ctor_set_uint8(v___x_4941_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4939_);
lean_ctor_set_uint8(v___x_4941_, sizeof(void*)*7 + 3, v_cacheInferType_4940_);
v___x_4942_ = lean_st_ref_take(v___y_4892_);
v_mctx_4943_ = lean_ctor_get(v___x_4942_, 0);
v_cache_4944_ = lean_ctor_get(v___x_4942_, 1);
v_zetaDeltaFVarIds_4945_ = lean_ctor_get(v___x_4942_, 2);
v_postponed_4946_ = lean_ctor_get(v___x_4942_, 3);
v_diag_4947_ = lean_ctor_get(v___x_4942_, 4);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4949_ = v___x_4942_;
v_isShared_4950_ = v_isSharedCheck_4999_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_diag_4947_);
lean_inc(v_postponed_4946_);
lean_inc(v_zetaDeltaFVarIds_4945_);
lean_inc(v_cache_4944_);
lean_inc(v_mctx_4943_);
lean_dec(v___x_4942_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4999_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v_a_4952_; lean_object* v_a_4956_; lean_object* v___y_4969_; lean_object* v___y_4973_; lean_object* v___x_4977_; 
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 2, v___x_4904_);
v___x_4977_ = v___x_4949_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_mctx_4943_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v_cache_4944_);
lean_ctor_set(v_reuseFailAlloc_4998_, 2, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4998_, 3, v_postponed_4946_);
lean_ctor_set(v_reuseFailAlloc_4998_, 4, v_diag_4947_);
v___x_4977_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4976_;
}
v___jp_4951_:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = lean_box(0);
v___x_4954_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4892_, v_zetaDeltaFVarIds_4945_, v___x_4953_);
lean_dec_ref(v___x_4954_);
v_a_4908_ = v_a_4952_;
goto v___jp_4907_;
}
v___jp_4955_:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_inc(v_a_4956_);
v___x_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_a_4956_);
v___x_4958_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4892_, v_zetaDeltaFVarIds_4945_, v___x_4957_);
lean_dec_ref(v___x_4958_);
v___x_4959_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4892_, v_cache_4906_, v___x_4957_);
lean_dec_ref_known(v___x_4957_, 1);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4966_ == 0)
{
lean_object* v_unused_4967_; 
v_unused_4967_ = lean_ctor_get(v___x_4959_, 0);
lean_dec(v_unused_4967_);
v___x_4961_ = v___x_4959_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_dec(v___x_4959_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 0, v_a_4956_);
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4956_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
v___jp_4968_:
{
if (lean_obj_tag(v___y_4969_) == 0)
{
lean_object* v_a_4970_; 
v_a_4970_ = lean_ctor_get(v___y_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref_known(v___y_4969_, 1);
v_a_4956_ = v_a_4970_;
goto v___jp_4955_;
}
else
{
lean_object* v_a_4971_; 
v_a_4971_ = lean_ctor_get(v___y_4969_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___y_4969_, 1);
v_a_4952_ = v_a_4971_;
goto v___jp_4951_;
}
}
v___jp_4972_:
{
if (lean_obj_tag(v___y_4973_) == 0)
{
lean_object* v_a_4974_; 
v_a_4974_ = lean_ctor_get(v___y_4973_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___y_4973_, 1);
v_a_4956_ = v_a_4974_;
goto v___jp_4955_;
}
else
{
lean_object* v_a_4975_; 
v_a_4975_ = lean_ctor_get(v___y_4973_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___y_4973_, 1);
v_a_4952_ = v_a_4975_;
goto v___jp_4951_;
}
}
v_reusejp_4976_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; uint8_t v_transparency_4980_; uint8_t v___x_4981_; 
v___x_4978_ = lean_st_ref_put(v___y_4892_, v___x_4977_);
v___x_4979_ = l_Lean_Meta_Context_config(v___x_4941_);
v_transparency_4980_ = lean_ctor_get_uint8(v___x_4979_, 9);
lean_dec_ref(v___x_4979_);
v___x_4981_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4980_, v___x_4899_);
if (v___x_4981_ == 0)
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v_transparency_4985_; uint8_t v___x_4986_; uint8_t v___x_4987_; 
lean_dec_ref_known(v___x_4941_, 7);
lean_inc_ref(v_keyedConfig_4931_);
v___x_4982_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4899_, v_keyedConfig_4931_);
lean_inc(v_customCanUnfoldPredicate_x3f_4937_);
lean_inc(v_synthPendingDepth_4936_);
lean_inc(v_defEqCtx_x3f_4935_);
lean_inc_ref(v_localInstances_4934_);
lean_inc_ref(v_lctx_4933_);
lean_inc(v_zetaDeltaSet_4932_);
lean_inc_ref(v___x_4982_);
v___x_4983_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
lean_ctor_set(v___x_4983_, 1, v_zetaDeltaSet_4932_);
lean_ctor_set(v___x_4983_, 2, v_lctx_4933_);
lean_ctor_set(v___x_4983_, 3, v_localInstances_4934_);
lean_ctor_set(v___x_4983_, 4, v_defEqCtx_x3f_4935_);
lean_ctor_set(v___x_4983_, 5, v_synthPendingDepth_4936_);
lean_ctor_set(v___x_4983_, 6, v_customCanUnfoldPredicate_x3f_4937_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*7, v___x_4888_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*7 + 1, v_univApprox_4938_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4939_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*7 + 3, v_cacheInferType_4940_);
v___x_4984_ = l_Lean_Meta_Context_config(v___x_4983_);
v_transparency_4985_ = lean_ctor_get_uint8(v___x_4984_, 9);
lean_dec_ref(v___x_4984_);
v___x_4986_ = 1;
v___x_4987_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4985_, v___x_4986_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; 
lean_dec_ref(v___x_4982_);
lean_inc(v___y_4894_);
lean_inc_ref(v___y_4893_);
lean_inc(v___y_4892_);
v___x_4988_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4888_, v___f_4903_, v___x_4983_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4969_ = v___x_4988_;
goto v___jp_4968_;
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
lean_dec_ref_known(v___x_4983_, 7);
v___x_4989_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4986_, v___x_4982_);
lean_inc(v_customCanUnfoldPredicate_x3f_4937_);
lean_inc(v_synthPendingDepth_4936_);
lean_inc(v_defEqCtx_x3f_4935_);
lean_inc_ref(v_localInstances_4934_);
lean_inc_ref(v_lctx_4933_);
lean_inc(v_zetaDeltaSet_4932_);
v___x_4990_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v_zetaDeltaSet_4932_);
lean_ctor_set(v___x_4990_, 2, v_lctx_4933_);
lean_ctor_set(v___x_4990_, 3, v_localInstances_4934_);
lean_ctor_set(v___x_4990_, 4, v_defEqCtx_x3f_4935_);
lean_ctor_set(v___x_4990_, 5, v_synthPendingDepth_4936_);
lean_ctor_set(v___x_4990_, 6, v_customCanUnfoldPredicate_x3f_4937_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7, v___x_4888_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7 + 1, v_univApprox_4938_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4939_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7 + 3, v_cacheInferType_4940_);
lean_inc(v___y_4894_);
lean_inc_ref(v___y_4893_);
lean_inc(v___y_4892_);
v___x_4991_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4888_, v___f_4903_, v___x_4990_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4969_ = v___x_4991_;
goto v___jp_4968_;
}
}
else
{
uint8_t v___x_4992_; uint8_t v___x_4993_; 
v___x_4992_ = 1;
v___x_4993_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4980_, v___x_4992_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; 
lean_inc(v___y_4894_);
lean_inc_ref(v___y_4893_);
lean_inc(v___y_4892_);
v___x_4994_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4981_, v___f_4903_, v___x_4941_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4973_ = v___x_4994_;
goto v___jp_4972_;
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
lean_dec_ref_known(v___x_4941_, 7);
lean_inc_ref(v_keyedConfig_4931_);
v___x_4995_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4992_, v_keyedConfig_4931_);
lean_inc(v_customCanUnfoldPredicate_x3f_4937_);
lean_inc(v_synthPendingDepth_4936_);
lean_inc(v_defEqCtx_x3f_4935_);
lean_inc_ref(v_localInstances_4934_);
lean_inc_ref(v_lctx_4933_);
lean_inc(v_zetaDeltaSet_4932_);
v___x_4996_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
lean_ctor_set(v___x_4996_, 1, v_zetaDeltaSet_4932_);
lean_ctor_set(v___x_4996_, 2, v_lctx_4933_);
lean_ctor_set(v___x_4996_, 3, v_localInstances_4934_);
lean_ctor_set(v___x_4996_, 4, v_defEqCtx_x3f_4935_);
lean_ctor_set(v___x_4996_, 5, v_synthPendingDepth_4936_);
lean_ctor_set(v___x_4996_, 6, v_customCanUnfoldPredicate_x3f_4937_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7, v___x_4888_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7 + 1, v_univApprox_4938_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4939_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7 + 3, v_cacheInferType_4940_);
lean_inc(v___y_4894_);
lean_inc_ref(v___y_4893_);
lean_inc(v___y_4892_);
v___x_4997_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4981_, v___f_4903_, v___x_4996_, v___y_4892_, v___y_4893_, v___y_4894_);
v___y_4973_ = v___x_4997_;
goto v___jp_4972_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_5003_, lean_object* v_e_5004_, lean_object* v_cls_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
uint8_t v___x_14226__boxed_5011_; lean_object* v_res_5012_; 
v___x_14226__boxed_5011_ = lean_unbox(v___x_5003_);
v_res_5012_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14226__boxed_5011_, v_e_5004_, v_cls_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
if (lean_obj_tag(v_x_5013_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5027_; 
v_a_5019_ = lean_ctor_get(v_x_5013_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_x_5013_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5021_ = v_x_5013_;
v_isShared_5022_ = v_isSharedCheck_5027_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v_x_5013_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5027_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5023_; lean_object* v___x_5025_; 
v___x_5023_ = l_Lean_Exception_toMessageData(v_a_5019_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v___x_5023_);
v___x_5025_ = v___x_5021_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5023_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5036_; 
v_a_5028_ = lean_ctor_get(v_x_5013_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v_x_5013_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5030_ = v_x_5013_;
v_isShared_5031_ = v_isSharedCheck_5036_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v_x_5013_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5036_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v_snd_5032_; lean_object* v___x_5034_; 
v_snd_5032_ = lean_ctor_get(v_a_5028_, 1);
lean_inc(v_snd_5032_);
lean_dec(v_a_5028_);
if (v_isShared_5031_ == 0)
{
lean_ctor_set_tag(v___x_5030_, 0);
lean_ctor_set(v___x_5030_, 0, v_snd_5032_);
v___x_5034_ = v___x_5030_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_snd_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec_ref(v___y_5038_);
return v_res_5043_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5044_){
_start:
{
if (lean_obj_tag(v_x_5044_) == 0)
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
v_a_5046_ = lean_ctor_get(v_x_5044_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v_x_5044_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v_x_5044_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v_x_5044_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
lean_ctor_set_tag(v___x_5048_, 1);
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
else
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
v_a_5054_ = lean_ctor_get(v_x_5044_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v_x_5044_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v_x_5044_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v_x_5044_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
lean_ctor_set_tag(v___x_5056_, 0);
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5062_, lean_object* v___y_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5062_);
return v_res_5064_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5065_){
_start:
{
if (lean_obj_tag(v_e_5065_) == 0)
{
uint8_t v___x_5066_; 
v___x_5066_ = 2;
return v___x_5066_;
}
else
{
uint8_t v___x_5067_; 
v___x_5067_ = 0;
return v___x_5067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5068_){
_start:
{
uint8_t v_res_5069_; lean_object* v_r_5070_; 
v_res_5069_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5068_);
lean_dec_ref(v_e_5068_);
v_r_5070_ = lean_box(v_res_5069_);
return v_r_5070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5071_, lean_object* v_data_5072_, lean_object* v_ref_5073_, lean_object* v_msg_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v_toCold_5080_; lean_object* v_currRecDepth_5081_; lean_object* v_ref_5082_; uint16_t v_optionFlags_5083_; uint8_t v_suppressElabErrors_5084_; uint8_t v_isRecordingDeps_5085_; lean_object* v_ref_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v_traceState_5089_; lean_object* v_traces_5090_; lean_object* v___x_5091_; size_t v_sz_5092_; size_t v___x_5093_; lean_object* v___x_5094_; lean_object* v_msg_5095_; lean_object* v___x_5096_; lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5135_; 
v_toCold_5080_ = lean_ctor_get(v___y_5077_, 0);
v_currRecDepth_5081_ = lean_ctor_get(v___y_5077_, 1);
v_ref_5082_ = lean_ctor_get(v___y_5077_, 2);
v_optionFlags_5083_ = lean_ctor_get_uint16(v___y_5077_, sizeof(void*)*3);
v_suppressElabErrors_5084_ = lean_ctor_get_uint8(v___y_5077_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5085_ = lean_ctor_get_uint8(v___y_5077_, sizeof(void*)*3 + 3);
v_ref_5086_ = l_Lean_replaceRef(v_ref_5073_, v_ref_5082_);
lean_inc(v_currRecDepth_5081_);
lean_inc_ref(v_toCold_5080_);
v___x_5087_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5087_, 0, v_toCold_5080_);
lean_ctor_set(v___x_5087_, 1, v_currRecDepth_5081_);
lean_ctor_set(v___x_5087_, 2, v_ref_5086_);
lean_ctor_set_uint16(v___x_5087_, sizeof(void*)*3, v_optionFlags_5083_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*3 + 2, v_suppressElabErrors_5084_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*3 + 3, v_isRecordingDeps_5085_);
v___x_5088_ = lean_st_ref_get(v___y_5078_);
v_traceState_5089_ = lean_ctor_get(v___x_5088_, 4);
lean_inc_ref(v_traceState_5089_);
lean_dec(v___x_5088_);
v_traces_5090_ = lean_ctor_get(v_traceState_5089_, 0);
lean_inc_ref(v_traces_5090_);
lean_dec_ref(v_traceState_5089_);
v___x_5091_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5090_);
lean_dec_ref(v_traces_5090_);
v_sz_5092_ = lean_array_size(v___x_5091_);
v___x_5093_ = ((size_t)0ULL);
v___x_5094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5092_, v___x_5093_, v___x_5091_);
v_msg_5095_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5095_, 0, v_data_5072_);
lean_ctor_set(v_msg_5095_, 1, v_msg_5074_);
lean_ctor_set(v_msg_5095_, 2, v___x_5094_);
v___x_5096_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5095_, v___y_5075_, v___y_5076_, v___x_5087_, v___y_5078_);
lean_dec_ref_known(v___x_5087_, 3);
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5135_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5135_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5101_; lean_object* v_traceState_5102_; lean_object* v_env_5103_; lean_object* v_nextMacroScope_5104_; lean_object* v_ngen_5105_; lean_object* v_auxDeclNGen_5106_; lean_object* v_cache_5107_; lean_object* v_recordedDeps_5108_; lean_object* v_messages_5109_; lean_object* v_infoState_5110_; lean_object* v_snapshotTasks_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5134_; 
v___x_5101_ = lean_st_ref_take(v___y_5078_);
v_traceState_5102_ = lean_ctor_get(v___x_5101_, 4);
v_env_5103_ = lean_ctor_get(v___x_5101_, 0);
v_nextMacroScope_5104_ = lean_ctor_get(v___x_5101_, 1);
v_ngen_5105_ = lean_ctor_get(v___x_5101_, 2);
v_auxDeclNGen_5106_ = lean_ctor_get(v___x_5101_, 3);
v_cache_5107_ = lean_ctor_get(v___x_5101_, 5);
v_recordedDeps_5108_ = lean_ctor_get(v___x_5101_, 6);
v_messages_5109_ = lean_ctor_get(v___x_5101_, 7);
v_infoState_5110_ = lean_ctor_get(v___x_5101_, 8);
v_snapshotTasks_5111_ = lean_ctor_get(v___x_5101_, 9);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5113_ = v___x_5101_;
v_isShared_5114_ = v_isSharedCheck_5134_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_snapshotTasks_5111_);
lean_inc(v_infoState_5110_);
lean_inc(v_messages_5109_);
lean_inc(v_recordedDeps_5108_);
lean_inc(v_cache_5107_);
lean_inc(v_traceState_5102_);
lean_inc(v_auxDeclNGen_5106_);
lean_inc(v_ngen_5105_);
lean_inc(v_nextMacroScope_5104_);
lean_inc(v_env_5103_);
lean_dec(v___x_5101_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5134_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
uint64_t v_tid_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5132_; 
v_tid_5115_ = lean_ctor_get_uint64(v_traceState_5102_, sizeof(void*)*1);
v_isSharedCheck_5132_ = !lean_is_exclusive(v_traceState_5102_);
if (v_isSharedCheck_5132_ == 0)
{
lean_object* v_unused_5133_; 
v_unused_5133_ = lean_ctor_get(v_traceState_5102_, 0);
lean_dec(v_unused_5133_);
v___x_5117_ = v_traceState_5102_;
v_isShared_5118_ = v_isSharedCheck_5132_;
goto v_resetjp_5116_;
}
else
{
lean_dec(v_traceState_5102_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5132_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5123_; 
v___x_5119_ = lean_box(0);
v___x_5120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5120_, 0, v_ref_5073_);
lean_ctor_set(v___x_5120_, 1, v_a_5097_);
v___x_5121_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5071_, v___x_5120_);
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 0, v___x_5121_);
v___x_5123_ = v___x_5117_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5121_);
lean_ctor_set_uint64(v_reuseFailAlloc_5131_, sizeof(void*)*1, v_tid_5115_);
v___x_5123_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
lean_object* v___x_5125_; 
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 4, v___x_5123_);
v___x_5125_ = v___x_5113_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_env_5103_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v_nextMacroScope_5104_);
lean_ctor_set(v_reuseFailAlloc_5130_, 2, v_ngen_5105_);
lean_ctor_set(v_reuseFailAlloc_5130_, 3, v_auxDeclNGen_5106_);
lean_ctor_set(v_reuseFailAlloc_5130_, 4, v___x_5123_);
lean_ctor_set(v_reuseFailAlloc_5130_, 5, v_cache_5107_);
lean_ctor_set(v_reuseFailAlloc_5130_, 6, v_recordedDeps_5108_);
lean_ctor_set(v_reuseFailAlloc_5130_, 7, v_messages_5109_);
lean_ctor_set(v_reuseFailAlloc_5130_, 8, v_infoState_5110_);
lean_ctor_set(v_reuseFailAlloc_5130_, 9, v_snapshotTasks_5111_);
v___x_5125_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
lean_object* v___x_5126_; lean_object* v___x_5128_; 
v___x_5126_ = lean_st_ref_put(v___y_5078_, v___x_5125_);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v___x_5119_);
v___x_5128_ = v___x_5099_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5119_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5136_, lean_object* v_data_5137_, lean_object* v_ref_5138_, lean_object* v_msg_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5136_, v_data_5137_, v_ref_5138_, v_msg_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5146_, uint8_t v_collapsed_5147_, lean_object* v_tag_5148_, lean_object* v_opts_5149_, uint8_t v_clsEnabled_5150_, lean_object* v_oldTraces_5151_, lean_object* v_msg_5152_, lean_object* v_resStartStop_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v_fst_5159_; lean_object* v_snd_5160_; lean_object* v___y_5162_; lean_object* v___y_5163_; lean_object* v_data_5164_; lean_object* v_fst_5175_; lean_object* v_snd_5176_; lean_object* v___x_5177_; uint8_t v___x_5178_; lean_object* v___y_5180_; lean_object* v_a_5181_; uint8_t v___y_5196_; double v___y_5228_; 
v_fst_5159_ = lean_ctor_get(v_resStartStop_5153_, 0);
lean_inc(v_fst_5159_);
v_snd_5160_ = lean_ctor_get(v_resStartStop_5153_, 1);
lean_inc(v_snd_5160_);
lean_dec_ref(v_resStartStop_5153_);
v_fst_5175_ = lean_ctor_get(v_snd_5160_, 0);
lean_inc(v_fst_5175_);
v_snd_5176_ = lean_ctor_get(v_snd_5160_, 1);
lean_inc(v_snd_5176_);
lean_dec(v_snd_5160_);
v___x_5177_ = l_Lean_trace_profiler;
v___x_5178_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5149_, v___x_5177_);
if (v___x_5178_ == 0)
{
v___y_5196_ = v___x_5178_;
goto v___jp_5195_;
}
else
{
lean_object* v___x_5233_; uint8_t v___x_5234_; 
v___x_5233_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5234_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5149_, v___x_5233_);
if (v___x_5234_ == 0)
{
lean_object* v___x_5235_; lean_object* v___x_5236_; double v___x_5237_; double v___x_5238_; double v___x_5239_; 
v___x_5235_ = l_Lean_trace_profiler_threshold;
v___x_5236_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5149_, v___x_5235_);
v___x_5237_ = lean_float_of_nat(v___x_5236_);
v___x_5238_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5239_ = lean_float_div(v___x_5237_, v___x_5238_);
v___y_5228_ = v___x_5239_;
goto v___jp_5227_;
}
else
{
lean_object* v___x_5240_; lean_object* v___x_5241_; double v___x_5242_; 
v___x_5240_ = l_Lean_trace_profiler_threshold;
v___x_5241_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5149_, v___x_5240_);
v___x_5242_ = lean_float_of_nat(v___x_5241_);
v___y_5228_ = v___x_5242_;
goto v___jp_5227_;
}
}
v___jp_5161_:
{
lean_object* v___x_5165_; 
lean_inc(v___y_5163_);
v___x_5165_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5151_, v_data_5164_, v___y_5163_, v___y_5162_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v___x_5166_; 
lean_dec_ref_known(v___x_5165_, 1);
v___x_5166_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5159_);
return v___x_5166_;
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
lean_dec(v_fst_5159_);
v_a_5167_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5165_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5165_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
v___jp_5179_:
{
uint8_t v_result_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; double v___x_5185_; lean_object* v_data_5186_; 
v_result_5182_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5159_);
v___x_5183_ = lean_box(v_result_5182_);
v___x_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5183_);
v___x_5185_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5148_);
lean_inc_ref(v___x_5184_);
lean_inc(v_cls_5146_);
v_data_5186_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5186_, 0, v_cls_5146_);
lean_ctor_set(v_data_5186_, 1, v___x_5184_);
lean_ctor_set(v_data_5186_, 2, v_tag_5148_);
lean_ctor_set_float(v_data_5186_, sizeof(void*)*3, v___x_5185_);
lean_ctor_set_float(v_data_5186_, sizeof(void*)*3 + 8, v___x_5185_);
lean_ctor_set_uint8(v_data_5186_, sizeof(void*)*3 + 16, v_collapsed_5147_);
if (v___x_5178_ == 0)
{
lean_dec_ref_known(v___x_5184_, 1);
lean_dec(v_snd_5176_);
lean_dec(v_fst_5175_);
lean_dec_ref(v_tag_5148_);
lean_dec(v_cls_5146_);
v___y_5162_ = v_a_5181_;
v___y_5163_ = v___y_5180_;
v_data_5164_ = v_data_5186_;
goto v___jp_5161_;
}
else
{
lean_object* v_data_5187_; double v___x_5188_; double v___x_5189_; 
lean_dec_ref_known(v_data_5186_, 3);
v_data_5187_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5187_, 0, v_cls_5146_);
lean_ctor_set(v_data_5187_, 1, v___x_5184_);
lean_ctor_set(v_data_5187_, 2, v_tag_5148_);
v___x_5188_ = lean_unbox_float(v_fst_5175_);
lean_dec(v_fst_5175_);
lean_ctor_set_float(v_data_5187_, sizeof(void*)*3, v___x_5188_);
v___x_5189_ = lean_unbox_float(v_snd_5176_);
lean_dec(v_snd_5176_);
lean_ctor_set_float(v_data_5187_, sizeof(void*)*3 + 8, v___x_5189_);
lean_ctor_set_uint8(v_data_5187_, sizeof(void*)*3 + 16, v_collapsed_5147_);
v___y_5162_ = v_a_5181_;
v___y_5163_ = v___y_5180_;
v_data_5164_ = v_data_5187_;
goto v___jp_5161_;
}
}
v___jp_5190_:
{
lean_object* v_ref_5191_; lean_object* v___x_5192_; 
v_ref_5191_ = lean_ctor_get(v___y_5156_, 2);
lean_inc(v___y_5157_);
lean_inc_ref(v___y_5156_);
lean_inc(v___y_5155_);
lean_inc_ref(v___y_5154_);
lean_inc(v_fst_5159_);
v___x_5192_ = lean_apply_6(v_msg_5152_, v_fst_5159_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, lean_box(0));
if (lean_obj_tag(v___x_5192_) == 0)
{
lean_object* v_a_5193_; 
v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
lean_inc(v_a_5193_);
lean_dec_ref_known(v___x_5192_, 1);
v___y_5180_ = v_ref_5191_;
v_a_5181_ = v_a_5193_;
goto v___jp_5179_;
}
else
{
lean_object* v___x_5194_; 
lean_dec_ref_known(v___x_5192_, 1);
v___x_5194_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5180_ = v_ref_5191_;
v_a_5181_ = v___x_5194_;
goto v___jp_5179_;
}
}
v___jp_5195_:
{
if (v_clsEnabled_5150_ == 0)
{
if (v___y_5196_ == 0)
{
lean_object* v___x_5197_; lean_object* v_traceState_5198_; lean_object* v_env_5199_; lean_object* v_nextMacroScope_5200_; lean_object* v_ngen_5201_; lean_object* v_auxDeclNGen_5202_; lean_object* v_cache_5203_; lean_object* v_recordedDeps_5204_; lean_object* v_messages_5205_; lean_object* v_infoState_5206_; lean_object* v_snapshotTasks_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5226_; 
lean_dec(v_snd_5176_);
lean_dec(v_fst_5175_);
lean_dec_ref(v_msg_5152_);
lean_dec_ref(v_tag_5148_);
lean_dec(v_cls_5146_);
v___x_5197_ = lean_st_ref_take(v___y_5157_);
v_traceState_5198_ = lean_ctor_get(v___x_5197_, 4);
v_env_5199_ = lean_ctor_get(v___x_5197_, 0);
v_nextMacroScope_5200_ = lean_ctor_get(v___x_5197_, 1);
v_ngen_5201_ = lean_ctor_get(v___x_5197_, 2);
v_auxDeclNGen_5202_ = lean_ctor_get(v___x_5197_, 3);
v_cache_5203_ = lean_ctor_get(v___x_5197_, 5);
v_recordedDeps_5204_ = lean_ctor_get(v___x_5197_, 6);
v_messages_5205_ = lean_ctor_get(v___x_5197_, 7);
v_infoState_5206_ = lean_ctor_get(v___x_5197_, 8);
v_snapshotTasks_5207_ = lean_ctor_get(v___x_5197_, 9);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5209_ = v___x_5197_;
v_isShared_5210_ = v_isSharedCheck_5226_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_snapshotTasks_5207_);
lean_inc(v_infoState_5206_);
lean_inc(v_messages_5205_);
lean_inc(v_recordedDeps_5204_);
lean_inc(v_cache_5203_);
lean_inc(v_traceState_5198_);
lean_inc(v_auxDeclNGen_5202_);
lean_inc(v_ngen_5201_);
lean_inc(v_nextMacroScope_5200_);
lean_inc(v_env_5199_);
lean_dec(v___x_5197_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5226_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
uint64_t v_tid_5211_; lean_object* v_traces_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5225_; 
v_tid_5211_ = lean_ctor_get_uint64(v_traceState_5198_, sizeof(void*)*1);
v_traces_5212_ = lean_ctor_get(v_traceState_5198_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_traceState_5198_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5214_ = v_traceState_5198_;
v_isShared_5215_ = v_isSharedCheck_5225_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_traces_5212_);
lean_dec(v_traceState_5198_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5225_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5216_; lean_object* v___x_5218_; 
v___x_5216_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5151_, v_traces_5212_);
lean_dec_ref(v_traces_5212_);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 0, v___x_5216_);
v___x_5218_ = v___x_5214_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5216_);
lean_ctor_set_uint64(v_reuseFailAlloc_5224_, sizeof(void*)*1, v_tid_5211_);
v___x_5218_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5220_; 
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 4, v___x_5218_);
v___x_5220_ = v___x_5209_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_env_5199_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_nextMacroScope_5200_);
lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_ngen_5201_);
lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_auxDeclNGen_5202_);
lean_ctor_set(v_reuseFailAlloc_5223_, 4, v___x_5218_);
lean_ctor_set(v_reuseFailAlloc_5223_, 5, v_cache_5203_);
lean_ctor_set(v_reuseFailAlloc_5223_, 6, v_recordedDeps_5204_);
lean_ctor_set(v_reuseFailAlloc_5223_, 7, v_messages_5205_);
lean_ctor_set(v_reuseFailAlloc_5223_, 8, v_infoState_5206_);
lean_ctor_set(v_reuseFailAlloc_5223_, 9, v_snapshotTasks_5207_);
v___x_5220_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5221_ = lean_st_ref_put(v___y_5157_, v___x_5220_);
v___x_5222_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5159_);
return v___x_5222_;
}
}
}
}
}
else
{
goto v___jp_5190_;
}
}
else
{
goto v___jp_5190_;
}
}
v___jp_5227_:
{
double v___x_5229_; double v___x_5230_; double v___x_5231_; uint8_t v___x_5232_; 
v___x_5229_ = lean_unbox_float(v_snd_5176_);
v___x_5230_ = lean_unbox_float(v_fst_5175_);
v___x_5231_ = lean_float_sub(v___x_5229_, v___x_5230_);
v___x_5232_ = lean_float_decLt(v___y_5228_, v___x_5231_);
v___y_5196_ = v___x_5232_;
goto v___jp_5195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5243_, lean_object* v_collapsed_5244_, lean_object* v_tag_5245_, lean_object* v_opts_5246_, lean_object* v_clsEnabled_5247_, lean_object* v_oldTraces_5248_, lean_object* v_msg_5249_, lean_object* v_resStartStop_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
uint8_t v_collapsed_boxed_5256_; uint8_t v_clsEnabled_boxed_5257_; lean_object* v_res_5258_; 
v_collapsed_boxed_5256_ = lean_unbox(v_collapsed_5244_);
v_clsEnabled_boxed_5257_ = lean_unbox(v_clsEnabled_5247_);
v_res_5258_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5243_, v_collapsed_boxed_5256_, v_tag_5245_, v_opts_5246_, v_clsEnabled_boxed_5257_, v_oldTraces_5248_, v_msg_5249_, v_resStartStop_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec_ref(v_opts_5246_);
return v_res_5258_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v_cls_5263_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5264_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5265_ = l_Lean_Name_append(v___x_5264_, v_cls_5263_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_){
_start:
{
lean_object* v___y_5273_; lean_object* v_toCold_5291_; lean_object* v_options_5292_; lean_object* v_inheritedTraceOptions_5293_; uint8_t v_hasTrace_5294_; lean_object* v_cls_5295_; uint8_t v___x_5296_; 
v_toCold_5291_ = lean_ctor_get(v_a_5269_, 0);
v_options_5292_ = lean_ctor_get(v_toCold_5291_, 2);
v_inheritedTraceOptions_5293_ = lean_ctor_get(v_toCold_5291_, 11);
v_hasTrace_5294_ = lean_ctor_get_uint8(v_options_5292_, sizeof(void*)*1);
v_cls_5295_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5296_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5266_);
if (v_hasTrace_5294_ == 0)
{
lean_object* v___x_5297_; 
v___x_5297_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5296_, v_e_5266_, v_cls_5295_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
v___y_5273_ = v___x_5297_;
goto v___jp_5272_;
}
else
{
lean_object* v___f_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; uint8_t v___x_5301_; lean_object* v___y_5303_; lean_object* v___y_5304_; lean_object* v_a_5305_; lean_object* v___y_5318_; lean_object* v___y_5319_; lean_object* v_a_5320_; 
v___f_5298_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5299_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5300_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5301_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5293_, v_options_5292_, v___x_5300_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5370_; uint8_t v___x_5371_; 
v___x_5370_ = l_Lean_trace_profiler;
v___x_5371_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5292_, v___x_5370_);
if (v___x_5371_ == 0)
{
lean_object* v___x_5372_; 
v___x_5372_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5296_, v_e_5266_, v_cls_5295_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
v___y_5273_ = v___x_5372_;
goto v___jp_5272_;
}
else
{
goto v___jp_5329_;
}
}
else
{
goto v___jp_5329_;
}
v___jp_5302_:
{
lean_object* v___x_5306_; double v___x_5307_; double v___x_5308_; double v___x_5309_; double v___x_5310_; double v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5306_ = lean_io_mono_nanos_now();
v___x_5307_ = lean_float_of_nat(v___y_5304_);
v___x_5308_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5309_ = lean_float_div(v___x_5307_, v___x_5308_);
v___x_5310_ = lean_float_of_nat(v___x_5306_);
v___x_5311_ = lean_float_div(v___x_5310_, v___x_5308_);
v___x_5312_ = lean_box_float(v___x_5309_);
v___x_5313_ = lean_box_float(v___x_5311_);
v___x_5314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5312_);
lean_ctor_set(v___x_5314_, 1, v___x_5313_);
v___x_5315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5315_, 0, v_a_5305_);
lean_ctor_set(v___x_5315_, 1, v___x_5314_);
v___x_5316_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5295_, v_hasTrace_5294_, v___x_5299_, v_options_5292_, v___x_5301_, v___y_5303_, v___f_5298_, v___x_5315_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
v___y_5273_ = v___x_5316_;
goto v___jp_5272_;
}
v___jp_5317_:
{
lean_object* v___x_5321_; double v___x_5322_; double v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5321_ = lean_io_get_num_heartbeats();
v___x_5322_ = lean_float_of_nat(v___y_5319_);
v___x_5323_ = lean_float_of_nat(v___x_5321_);
v___x_5324_ = lean_box_float(v___x_5322_);
v___x_5325_ = lean_box_float(v___x_5323_);
v___x_5326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5326_, 0, v___x_5324_);
lean_ctor_set(v___x_5326_, 1, v___x_5325_);
v___x_5327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5327_, 0, v_a_5320_);
lean_ctor_set(v___x_5327_, 1, v___x_5326_);
v___x_5328_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5295_, v_hasTrace_5294_, v___x_5299_, v_options_5292_, v___x_5301_, v___y_5318_, v___f_5298_, v___x_5327_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
v___y_5273_ = v___x_5328_;
goto v___jp_5272_;
}
v___jp_5329_:
{
lean_object* v___x_5330_; lean_object* v_a_5331_; lean_object* v___x_5332_; uint8_t v___x_5333_; 
v___x_5330_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5270_);
v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
lean_inc(v_a_5331_);
lean_dec_ref(v___x_5330_);
v___x_5332_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5333_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5292_, v___x_5332_);
if (v___x_5333_ == 0)
{
lean_object* v___x_5334_; lean_object* v___x_5335_; 
v___x_5334_ = lean_io_mono_nanos_now();
v___x_5335_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5296_, v_e_5266_, v_cls_5295_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5335_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5335_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
lean_ctor_set_tag(v___x_5338_, 1);
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
v___y_5303_ = v_a_5331_;
v___y_5304_ = v___x_5334_;
v_a_5305_ = v___x_5341_;
goto v___jp_5302_;
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
v_a_5344_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5335_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5335_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
lean_ctor_set_tag(v___x_5346_, 0);
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
v___y_5303_ = v_a_5331_;
v___y_5304_ = v___x_5334_;
v_a_5305_ = v___x_5349_;
goto v___jp_5302_;
}
}
}
}
else
{
lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5352_ = lean_io_get_num_heartbeats();
v___x_5353_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5296_, v_e_5266_, v_cls_5295_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
if (lean_obj_tag(v___x_5353_) == 0)
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5353_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5353_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5353_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
lean_ctor_set_tag(v___x_5356_, 1);
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
v___y_5318_ = v_a_5331_;
v___y_5319_ = v___x_5352_;
v_a_5320_ = v___x_5359_;
goto v___jp_5317_;
}
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
v_a_5362_ = lean_ctor_get(v___x_5353_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5353_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5353_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5353_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
lean_ctor_set_tag(v___x_5364_, 0);
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
v___y_5318_ = v_a_5331_;
v___y_5319_ = v___x_5352_;
v_a_5320_ = v___x_5367_;
goto v___jp_5317_;
}
}
}
}
}
}
v___jp_5272_:
{
if (lean_obj_tag(v___y_5273_) == 0)
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5282_; 
v_a_5274_ = lean_ctor_get(v___y_5273_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___y_5273_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5276_ = v___y_5273_;
v_isShared_5277_ = v_isSharedCheck_5282_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___y_5273_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5282_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v_fst_5278_; lean_object* v___x_5280_; 
v_fst_5278_ = lean_ctor_get(v_a_5274_, 0);
lean_inc(v_fst_5278_);
lean_dec(v_a_5274_);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 0, v_fst_5278_);
v___x_5280_ = v___x_5276_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_fst_5278_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
else
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5290_; 
v_a_5283_ = lean_ctor_get(v___y_5273_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___y_5273_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5285_ = v___y_5273_;
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___y_5273_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v___x_5288_; 
if (v_isShared_5286_ == 0)
{
v___x_5288_ = v___x_5285_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_a_5283_);
v___x_5288_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
return v___x_5288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
lean_dec(v_a_5375_);
lean_dec_ref(v_a_5374_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5380_, lean_object* v_x_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_){
_start:
{
lean_object* v___x_5387_; 
v___x_5387_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5381_);
return v___x_5387_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5388_, lean_object* v_x_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5388_, v_x_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5396_, lean_object* v___y_5397_){
_start:
{
uint8_t v___x_5399_; 
v___x_5399_ = l_Lean_Expr_hasMVar(v_e_5396_);
if (v___x_5399_ == 0)
{
lean_object* v___x_5400_; 
v___x_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5400_, 0, v_e_5396_);
return v___x_5400_;
}
else
{
lean_object* v___x_5401_; lean_object* v_mctx_5402_; lean_object* v___x_5403_; lean_object* v_fst_5404_; lean_object* v_snd_5405_; lean_object* v___x_5406_; lean_object* v_cache_5407_; lean_object* v_zetaDeltaFVarIds_5408_; lean_object* v_postponed_5409_; lean_object* v_diag_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5419_; 
v___x_5401_ = lean_st_ref_get(v___y_5397_);
v_mctx_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc_ref(v_mctx_5402_);
lean_dec(v___x_5401_);
v___x_5403_ = l_Lean_instantiateMVarsCore(v_mctx_5402_, v_e_5396_);
v_fst_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_fst_5404_);
v_snd_5405_ = lean_ctor_get(v___x_5403_, 1);
lean_inc(v_snd_5405_);
lean_dec_ref(v___x_5403_);
v___x_5406_ = lean_st_ref_take(v___y_5397_);
v_cache_5407_ = lean_ctor_get(v___x_5406_, 1);
v_zetaDeltaFVarIds_5408_ = lean_ctor_get(v___x_5406_, 2);
v_postponed_5409_ = lean_ctor_get(v___x_5406_, 3);
v_diag_5410_ = lean_ctor_get(v___x_5406_, 4);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5419_ == 0)
{
lean_object* v_unused_5420_; 
v_unused_5420_ = lean_ctor_get(v___x_5406_, 0);
lean_dec(v_unused_5420_);
v___x_5412_ = v___x_5406_;
v_isShared_5413_ = v_isSharedCheck_5419_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_diag_5410_);
lean_inc(v_postponed_5409_);
lean_inc(v_zetaDeltaFVarIds_5408_);
lean_inc(v_cache_5407_);
lean_dec(v___x_5406_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5419_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5415_; 
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 0, v_snd_5405_);
v___x_5415_ = v___x_5412_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_snd_5405_);
lean_ctor_set(v_reuseFailAlloc_5418_, 1, v_cache_5407_);
lean_ctor_set(v_reuseFailAlloc_5418_, 2, v_zetaDeltaFVarIds_5408_);
lean_ctor_set(v_reuseFailAlloc_5418_, 3, v_postponed_5409_);
lean_ctor_set(v_reuseFailAlloc_5418_, 4, v_diag_5410_);
v___x_5415_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = lean_st_ref_put(v___y_5397_, v___x_5415_);
v___x_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5417_, 0, v_fst_5404_);
return v___x_5417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5421_, v___y_5422_);
lean_dec(v___y_5422_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_){
_start:
{
lean_object* v___x_5431_; 
v___x_5431_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5425_, v___y_5427_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5439_, lean_object* v_opts_5440_, lean_object* v_act_5441_, lean_object* v_decl_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_){
_start:
{
lean_object* v___x_5448_; lean_object* v___x_5449_; 
lean_inc(v___y_5446_);
lean_inc_ref(v___y_5445_);
lean_inc(v___y_5444_);
lean_inc_ref(v___y_5443_);
v___x_5448_ = lean_apply_4(v_act_5441_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_);
v___x_5449_ = l_Lean_profileitIOUnsafe___redArg(v_category_5439_, v_opts_5440_, v___x_5448_, v_decl_5442_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5450_, lean_object* v_opts_5451_, lean_object* v_act_5452_, lean_object* v_decl_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5450_, v_opts_5451_, v_act_5452_, v_decl_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec_ref(v_opts_5451_);
lean_dec_ref(v_category_5450_);
return v_res_5459_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5460_, lean_object* v_category_5461_, lean_object* v_opts_5462_, lean_object* v_act_5463_, lean_object* v_decl_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v___x_5470_; 
v___x_5470_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5461_, v_opts_5462_, v_act_5463_, v_decl_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5471_, lean_object* v_category_5472_, lean_object* v_opts_5473_, lean_object* v_act_5474_, lean_object* v_decl_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_){
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5471_, v_category_5472_, v_opts_5473_, v_act_5474_, v_decl_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec_ref(v_opts_5473_);
lean_dec_ref(v_category_5472_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5482_, uint8_t v_isExporting_5483_, lean_object* v___x_5484_, lean_object* v___y_5485_, lean_object* v___x_5486_, lean_object* v_a_x3f_5487_){
_start:
{
lean_object* v___x_5489_; lean_object* v_env_5490_; lean_object* v_nextMacroScope_5491_; lean_object* v_ngen_5492_; lean_object* v_auxDeclNGen_5493_; lean_object* v_traceState_5494_; lean_object* v_recordedDeps_5495_; lean_object* v_messages_5496_; lean_object* v_infoState_5497_; lean_object* v_snapshotTasks_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5523_; 
v___x_5489_ = lean_st_ref_take(v___y_5482_);
v_env_5490_ = lean_ctor_get(v___x_5489_, 0);
v_nextMacroScope_5491_ = lean_ctor_get(v___x_5489_, 1);
v_ngen_5492_ = lean_ctor_get(v___x_5489_, 2);
v_auxDeclNGen_5493_ = lean_ctor_get(v___x_5489_, 3);
v_traceState_5494_ = lean_ctor_get(v___x_5489_, 4);
v_recordedDeps_5495_ = lean_ctor_get(v___x_5489_, 6);
v_messages_5496_ = lean_ctor_get(v___x_5489_, 7);
v_infoState_5497_ = lean_ctor_get(v___x_5489_, 8);
v_snapshotTasks_5498_ = lean_ctor_get(v___x_5489_, 9);
v_isSharedCheck_5523_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5523_ == 0)
{
lean_object* v_unused_5524_; 
v_unused_5524_ = lean_ctor_get(v___x_5489_, 5);
lean_dec(v_unused_5524_);
v___x_5500_ = v___x_5489_;
v_isShared_5501_ = v_isSharedCheck_5523_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_snapshotTasks_5498_);
lean_inc(v_infoState_5497_);
lean_inc(v_messages_5496_);
lean_inc(v_recordedDeps_5495_);
lean_inc(v_traceState_5494_);
lean_inc(v_auxDeclNGen_5493_);
lean_inc(v_ngen_5492_);
lean_inc(v_nextMacroScope_5491_);
lean_inc(v_env_5490_);
lean_dec(v___x_5489_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5523_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5502_; lean_object* v___x_5504_; 
v___x_5502_ = l_Lean_Environment_setExporting(v_env_5490_, v_isExporting_5483_);
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 5, v___x_5484_);
lean_ctor_set(v___x_5500_, 0, v___x_5502_);
v___x_5504_ = v___x_5500_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5502_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v_nextMacroScope_5491_);
lean_ctor_set(v_reuseFailAlloc_5522_, 2, v_ngen_5492_);
lean_ctor_set(v_reuseFailAlloc_5522_, 3, v_auxDeclNGen_5493_);
lean_ctor_set(v_reuseFailAlloc_5522_, 4, v_traceState_5494_);
lean_ctor_set(v_reuseFailAlloc_5522_, 5, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5522_, 6, v_recordedDeps_5495_);
lean_ctor_set(v_reuseFailAlloc_5522_, 7, v_messages_5496_);
lean_ctor_set(v_reuseFailAlloc_5522_, 8, v_infoState_5497_);
lean_ctor_set(v_reuseFailAlloc_5522_, 9, v_snapshotTasks_5498_);
v___x_5504_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v_mctx_5507_; lean_object* v_zetaDeltaFVarIds_5508_; lean_object* v_postponed_5509_; lean_object* v_diag_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5520_; 
v___x_5505_ = lean_st_ref_put(v___y_5482_, v___x_5504_);
v___x_5506_ = lean_st_ref_take(v___y_5485_);
v_mctx_5507_ = lean_ctor_get(v___x_5506_, 0);
v_zetaDeltaFVarIds_5508_ = lean_ctor_get(v___x_5506_, 2);
v_postponed_5509_ = lean_ctor_get(v___x_5506_, 3);
v_diag_5510_ = lean_ctor_get(v___x_5506_, 4);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5520_ == 0)
{
lean_object* v_unused_5521_; 
v_unused_5521_ = lean_ctor_get(v___x_5506_, 1);
lean_dec(v_unused_5521_);
v___x_5512_ = v___x_5506_;
v_isShared_5513_ = v_isSharedCheck_5520_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_diag_5510_);
lean_inc(v_postponed_5509_);
lean_inc(v_zetaDeltaFVarIds_5508_);
lean_inc(v_mctx_5507_);
lean_dec(v___x_5506_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5520_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5514_; lean_object* v___x_5516_; 
v___x_5514_ = lean_box(0);
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 1, v___x_5486_);
v___x_5516_ = v___x_5512_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_mctx_5507_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5519_, 2, v_zetaDeltaFVarIds_5508_);
lean_ctor_set(v_reuseFailAlloc_5519_, 3, v_postponed_5509_);
lean_ctor_set(v_reuseFailAlloc_5519_, 4, v_diag_5510_);
v___x_5516_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; 
v___x_5517_ = lean_st_ref_put(v___y_5485_, v___x_5516_);
v___x_5518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5514_);
return v___x_5518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5525_, lean_object* v_isExporting_5526_, lean_object* v___x_5527_, lean_object* v___y_5528_, lean_object* v___x_5529_, lean_object* v_a_x3f_5530_, lean_object* v___y_5531_){
_start:
{
uint8_t v_isExporting_boxed_5532_; lean_object* v_res_5533_; 
v_isExporting_boxed_5532_ = lean_unbox(v_isExporting_5526_);
v_res_5533_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5525_, v_isExporting_boxed_5532_, v___x_5527_, v___y_5528_, v___x_5529_, v_a_x3f_5530_);
lean_dec(v_a_x3f_5530_);
lean_dec(v___y_5528_);
lean_dec(v___y_5525_);
return v_res_5533_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5534_; lean_object* v___x_5535_; 
v___x_5534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_5535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5535_, 0, v___x_5534_);
return v___x_5535_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5536_);
lean_ctor_set(v___x_5537_, 1, v___x_5536_);
return v___x_5537_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
v___x_5538_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5539_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5538_);
lean_ctor_set(v___x_5539_, 1, v___x_5538_);
lean_ctor_set(v___x_5539_, 2, v___x_5538_);
lean_ctor_set(v___x_5539_, 3, v___x_5538_);
lean_ctor_set(v___x_5539_, 4, v___x_5538_);
lean_ctor_set(v___x_5539_, 5, v___x_5538_);
return v___x_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5540_, uint8_t v_isExporting_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v___x_5547_; lean_object* v_env_5548_; lean_object* v___x_5549_; uint8_t v_isModule_5550_; 
v___x_5547_ = lean_st_ref_get(v___y_5545_);
v_env_5548_ = lean_ctor_get(v___x_5547_, 0);
lean_inc_ref(v_env_5548_);
lean_dec(v___x_5547_);
v___x_5549_ = l_Lean_Environment_header(v_env_5548_);
v_isModule_5550_ = lean_ctor_get_uint8(v___x_5549_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5549_);
if (v_isModule_5550_ == 0)
{
lean_object* v___x_5551_; 
lean_dec_ref(v_env_5548_);
lean_inc(v___y_5545_);
lean_inc_ref(v___y_5544_);
lean_inc(v___y_5543_);
lean_inc_ref(v___y_5542_);
v___x_5551_ = lean_apply_5(v_x_5540_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, lean_box(0));
return v___x_5551_;
}
else
{
uint8_t v_isExporting_5552_; 
v_isExporting_5552_ = lean_ctor_get_uint8(v_env_5548_, sizeof(void*)*13);
lean_dec_ref(v_env_5548_);
if (v_isExporting_5541_ == 0)
{
if (v_isExporting_5552_ == 0)
{
lean_object* v___x_5619_; 
lean_inc(v___y_5545_);
lean_inc_ref(v___y_5544_);
lean_inc(v___y_5543_);
lean_inc_ref(v___y_5542_);
v___x_5619_ = lean_apply_5(v_x_5540_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, lean_box(0));
return v___x_5619_;
}
else
{
goto v___jp_5553_;
}
}
else
{
if (v_isExporting_5552_ == 0)
{
goto v___jp_5553_;
}
else
{
lean_object* v___x_5620_; 
lean_inc(v___y_5545_);
lean_inc_ref(v___y_5544_);
lean_inc(v___y_5543_);
lean_inc_ref(v___y_5542_);
v___x_5620_ = lean_apply_5(v_x_5540_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, lean_box(0));
return v___x_5620_;
}
}
v___jp_5553_:
{
lean_object* v___x_5554_; lean_object* v_env_5555_; lean_object* v_nextMacroScope_5556_; lean_object* v_ngen_5557_; lean_object* v_auxDeclNGen_5558_; lean_object* v_traceState_5559_; lean_object* v_recordedDeps_5560_; lean_object* v_messages_5561_; lean_object* v_infoState_5562_; lean_object* v_snapshotTasks_5563_; lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5617_; 
v___x_5554_ = lean_st_ref_take(v___y_5545_);
v_env_5555_ = lean_ctor_get(v___x_5554_, 0);
v_nextMacroScope_5556_ = lean_ctor_get(v___x_5554_, 1);
v_ngen_5557_ = lean_ctor_get(v___x_5554_, 2);
v_auxDeclNGen_5558_ = lean_ctor_get(v___x_5554_, 3);
v_traceState_5559_ = lean_ctor_get(v___x_5554_, 4);
v_recordedDeps_5560_ = lean_ctor_get(v___x_5554_, 6);
v_messages_5561_ = lean_ctor_get(v___x_5554_, 7);
v_infoState_5562_ = lean_ctor_get(v___x_5554_, 8);
v_snapshotTasks_5563_ = lean_ctor_get(v___x_5554_, 9);
v_isSharedCheck_5617_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5617_ == 0)
{
lean_object* v_unused_5618_; 
v_unused_5618_ = lean_ctor_get(v___x_5554_, 5);
lean_dec(v_unused_5618_);
v___x_5565_ = v___x_5554_;
v_isShared_5566_ = v_isSharedCheck_5617_;
goto v_resetjp_5564_;
}
else
{
lean_inc(v_snapshotTasks_5563_);
lean_inc(v_infoState_5562_);
lean_inc(v_messages_5561_);
lean_inc(v_recordedDeps_5560_);
lean_inc(v_traceState_5559_);
lean_inc(v_auxDeclNGen_5558_);
lean_inc(v_ngen_5557_);
lean_inc(v_nextMacroScope_5556_);
lean_inc(v_env_5555_);
lean_dec(v___x_5554_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5617_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5570_; 
v___x_5567_ = l_Lean_Environment_setExporting(v_env_5555_, v_isExporting_5541_);
v___x_5568_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 5, v___x_5568_);
lean_ctor_set(v___x_5565_, 0, v___x_5567_);
v___x_5570_ = v___x_5565_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v___x_5567_);
lean_ctor_set(v_reuseFailAlloc_5616_, 1, v_nextMacroScope_5556_);
lean_ctor_set(v_reuseFailAlloc_5616_, 2, v_ngen_5557_);
lean_ctor_set(v_reuseFailAlloc_5616_, 3, v_auxDeclNGen_5558_);
lean_ctor_set(v_reuseFailAlloc_5616_, 4, v_traceState_5559_);
lean_ctor_set(v_reuseFailAlloc_5616_, 5, v___x_5568_);
lean_ctor_set(v_reuseFailAlloc_5616_, 6, v_recordedDeps_5560_);
lean_ctor_set(v_reuseFailAlloc_5616_, 7, v_messages_5561_);
lean_ctor_set(v_reuseFailAlloc_5616_, 8, v_infoState_5562_);
lean_ctor_set(v_reuseFailAlloc_5616_, 9, v_snapshotTasks_5563_);
v___x_5570_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v_mctx_5573_; lean_object* v_zetaDeltaFVarIds_5574_; lean_object* v_postponed_5575_; lean_object* v_diag_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5614_; 
v___x_5571_ = lean_st_ref_put(v___y_5545_, v___x_5570_);
v___x_5572_ = lean_st_ref_take(v___y_5543_);
v_mctx_5573_ = lean_ctor_get(v___x_5572_, 0);
v_zetaDeltaFVarIds_5574_ = lean_ctor_get(v___x_5572_, 2);
v_postponed_5575_ = lean_ctor_get(v___x_5572_, 3);
v_diag_5576_ = lean_ctor_get(v___x_5572_, 4);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v___x_5572_, 1);
lean_dec(v_unused_5615_);
v___x_5578_ = v___x_5572_;
v_isShared_5579_ = v_isSharedCheck_5614_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_diag_5576_);
lean_inc(v_postponed_5575_);
lean_inc(v_zetaDeltaFVarIds_5574_);
lean_inc(v_mctx_5573_);
lean_dec(v___x_5572_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5614_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5580_; lean_object* v___x_5582_; 
v___x_5580_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 1, v___x_5580_);
v___x_5582_ = v___x_5578_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_mctx_5573_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v___x_5580_);
lean_ctor_set(v_reuseFailAlloc_5613_, 2, v_zetaDeltaFVarIds_5574_);
lean_ctor_set(v_reuseFailAlloc_5613_, 3, v_postponed_5575_);
lean_ctor_set(v_reuseFailAlloc_5613_, 4, v_diag_5576_);
v___x_5582_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
lean_object* v___x_5583_; lean_object* v_r_5584_; 
v___x_5583_ = lean_st_ref_put(v___y_5543_, v___x_5582_);
lean_inc(v___y_5545_);
lean_inc_ref(v___y_5544_);
lean_inc(v___y_5543_);
lean_inc_ref(v___y_5542_);
v_r_5584_ = lean_apply_5(v_x_5540_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, lean_box(0));
if (lean_obj_tag(v_r_5584_) == 0)
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5601_; 
v_a_5585_ = lean_ctor_get(v_r_5584_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v_r_5584_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5587_ = v_r_5584_;
v_isShared_5588_ = v_isSharedCheck_5601_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v_r_5584_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5601_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
lean_inc(v_a_5585_);
if (v_isShared_5588_ == 0)
{
lean_ctor_set_tag(v___x_5587_, 1);
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
lean_object* v___x_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5598_; 
v___x_5591_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5545_, v_isExporting_5552_, v___x_5568_, v___y_5543_, v___x_5580_, v___x_5590_);
lean_dec_ref(v___x_5590_);
v_isSharedCheck_5598_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5598_ == 0)
{
lean_object* v_unused_5599_; 
v_unused_5599_ = lean_ctor_get(v___x_5591_, 0);
lean_dec(v_unused_5599_);
v___x_5593_ = v___x_5591_;
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
else
{
lean_dec(v___x_5591_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5596_; 
if (v_isShared_5594_ == 0)
{
lean_ctor_set(v___x_5593_, 0, v_a_5585_);
v___x_5596_ = v___x_5593_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5585_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
return v___x_5596_;
}
}
}
}
}
else
{
lean_object* v_a_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5611_; 
v_a_5602_ = lean_ctor_get(v_r_5584_, 0);
lean_inc(v_a_5602_);
lean_dec_ref_known(v_r_5584_, 1);
v___x_5603_ = lean_box(0);
v___x_5604_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5545_, v_isExporting_5552_, v___x_5568_, v___y_5543_, v___x_5580_, v___x_5603_);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5604_);
if (v_isSharedCheck_5611_ == 0)
{
lean_object* v_unused_5612_; 
v_unused_5612_ = lean_ctor_get(v___x_5604_, 0);
lean_dec(v_unused_5612_);
v___x_5606_ = v___x_5604_;
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
else
{
lean_dec(v___x_5604_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
lean_ctor_set_tag(v___x_5606_, 1);
lean_ctor_set(v___x_5606_, 0, v_a_5602_);
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5602_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5621_, lean_object* v_isExporting_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
uint8_t v_isExporting_boxed_5628_; lean_object* v_res_5629_; 
v_isExporting_boxed_5628_ = lean_unbox(v_isExporting_5622_);
v_res_5629_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5621_, v_isExporting_boxed_5628_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_);
lean_dec(v___y_5626_);
lean_dec_ref(v___y_5625_);
lean_dec(v___y_5624_);
lean_dec_ref(v___y_5623_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5630_, uint8_t v_when_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_){
_start:
{
if (v_when_5631_ == 0)
{
lean_object* v___x_5637_; 
lean_inc(v___y_5635_);
lean_inc_ref(v___y_5634_);
lean_inc(v___y_5633_);
lean_inc_ref(v___y_5632_);
v___x_5637_ = lean_apply_5(v_x_5630_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, lean_box(0));
return v___x_5637_;
}
else
{
uint8_t v___x_5638_; lean_object* v___x_5639_; 
v___x_5638_ = 0;
v___x_5639_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5630_, v___x_5638_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
return v___x_5639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5640_, lean_object* v_when_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_){
_start:
{
uint8_t v_when_boxed_5647_; lean_object* v_res_5648_; 
v_when_boxed_5647_ = lean_unbox(v_when_5641_);
v_res_5648_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5640_, v_when_boxed_5647_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_){
_start:
{
lean_object* v___x_5655_; lean_object* v_a_5656_; lean_object* v___x_5657_; uint8_t v___x_5658_; lean_object* v___x_5659_; 
v___x_5655_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5649_, v___y_5651_);
v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc(v_a_5656_);
lean_dec_ref(v___x_5655_);
v___x_5657_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5657_, 0, v_a_5656_);
v___x_5658_ = 1;
v___x_5659_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5657_, v___x_5658_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_);
return v___x_5659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l_Lean_Meta_letToHave___lam__0(v_e_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_){
_start:
{
lean_object* v___f_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; 
v___f_5674_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5674_, 0, v_e_5668_);
v___x_5675_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5671_);
v___x_5676_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5677_ = lean_box(0);
v___x_5678_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5676_, v___x_5675_, v___f_5674_, v___x_5677_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_);
lean_dec_ref(v___x_5675_);
return v___x_5678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l_Lean_Meta_letToHave(v_e_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_);
lean_dec(v_a_5683_);
lean_dec_ref(v_a_5682_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5686_, lean_object* v_x_5687_, uint8_t v_isExporting_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v___x_5694_; 
v___x_5694_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5687_, v_isExporting_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
return v___x_5694_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5695_, lean_object* v_x_5696_, lean_object* v_isExporting_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_){
_start:
{
uint8_t v_isExporting_boxed_5703_; lean_object* v_res_5704_; 
v_isExporting_boxed_5703_ = lean_unbox(v_isExporting_5697_);
v_res_5704_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5695_, v_x_5696_, v_isExporting_boxed_5703_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5705_, lean_object* v_x_5706_, uint8_t v_when_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_){
_start:
{
lean_object* v___x_5713_; 
v___x_5713_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5706_, v_when_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
return v___x_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5714_, lean_object* v_x_5715_, lean_object* v_when_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
uint8_t v_when_boxed_5722_; lean_object* v_res_5723_; 
v_when_boxed_5722_ = lean_unbox(v_when_5716_);
v_res_5723_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5714_, v_x_5715_, v_when_boxed_5722_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5780_; uint8_t v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5780_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5781_ = 0;
v___x_5782_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5783_ = l_Lean_registerTraceClass(v___x_5780_, v___x_5781_, v___x_5782_);
if (lean_obj_tag(v___x_5783_) == 0)
{
lean_object* v___x_5784_; lean_object* v___x_5785_; 
lean_dec_ref_known(v___x_5783_, 1);
v___x_5784_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5785_ = l_Lean_registerTraceClass(v___x_5784_, v___x_5781_, v___x_5782_);
return v___x_5785_;
}
else
{
return v___x_5783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5786_){
_start:
{
lean_object* v_res_5787_; 
v_res_5787_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5787_;
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
