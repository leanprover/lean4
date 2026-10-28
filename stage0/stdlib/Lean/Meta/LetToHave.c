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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static const lean_array_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 3, 170, 90, 194, 179, 10, 17)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0));
v___x_739_ = lean_box(1);
v___x_740_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_739_, v___x_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object* v_a_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_796_; 
v_fst_749_ = lean_ctor_get(v_a_741_, 0);
v_snd_750_ = lean_ctor_get(v_a_741_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_a_741_);
if (v_isSharedCheck_796_ == 0)
{
v___x_752_ = v_a_741_;
v_isShared_753_ = v_isSharedCheck_796_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_inc(v_fst_749_);
lean_dec(v_a_741_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_796_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = lean_array_get_size(v_snd_750_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_nat_dec_eq(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_757_ = l_Lean_instInhabitedExpr;
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_nat_sub(v___x_754_, v___x_758_);
v___x_760_ = lean_array_get_borrowed(v___x_757_, v_snd_750_, v___x_759_);
lean_dec(v___x_759_);
lean_inc(v___x_760_);
v___x_761_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v___x_760_, v___y_745_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_fvarIds_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_764_ = l_Lean_collectFVars(v___x_763_, v_a_762_);
v_fvarIds_765_ = lean_ctor_get(v___x_764_, 2);
lean_inc_ref(v_fvarIds_765_);
lean_dec_ref(v___x_764_);
v___x_766_ = lean_array_pop(v_snd_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_766_);
v___x_768_ = v___x_752_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_fst_749_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_783_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
size_t v_sz_769_; size_t v___x_770_; lean_object* v___x_771_; 
v_sz_769_ = lean_array_size(v_fvarIds_765_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_fvarIds_765_, v_sz_769_, v___x_770_, v___x_768_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec_ref(v_fvarIds_765_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v_fst_773_; lean_object* v_snd_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v_fst_773_ = lean_ctor_get(v_a_772_, 0);
v_snd_774_ = lean_ctor_get(v_a_772_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v_a_772_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_snd_774_);
lean_inc(v_fst_773_);
lean_dec(v_a_772_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_fst_773_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_snd_774_);
v___x_779_ = v_reuseFailAlloc_781_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
v_a_741_ = v___x_779_;
goto _start;
}
}
}
else
{
return v___x_771_;
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_752_);
lean_dec(v_snd_750_);
lean_dec(v_fst_749_);
v_a_784_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_761_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_761_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v___x_793_; 
if (v_isShared_753_ == 0)
{
v___x_793_ = v___x_752_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_749_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_750_);
v___x_793_ = v_reuseFailAlloc_795_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object* v_a_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object* v_e_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_visited_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_worklist_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_visited_814_ = lean_box(1);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_mk_empty_array_with_capacity(v___x_815_);
v_worklist_817_ = lean_array_push(v___x_816_, v_e_806_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_visited_814_);
lean_ctor_set(v___x_818_, 1, v_worklist_817_);
v___x_819_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v___x_818_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_819_, 0);
lean_dec(v_unused_828_);
v___x_821_ = v___x_819_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_dec(v___x_819_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_box(0);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_819_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object* v_e_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v_e_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec(v_a_838_);
return v_res_845_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object* v_00_u03b2_846_, lean_object* v_k_847_, lean_object* v_t_848_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_847_, v_t_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object* v_00_u03b2_850_, lean_object* v_k_851_, lean_object* v_t_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(v_00_u03b2_850_, v_k_851_, v_t_852_);
lean_dec(v_t_852_);
lean_dec(v_k_851_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object* v_as_855_, size_t v_sz_856_, size_t v_i_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_855_, v_sz_856_, v_i_857_, v_b_858_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object* v_as_867_, lean_object* v_sz_868_, lean_object* v_i_869_, lean_object* v_b_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
size_t v_sz_boxed_878_; size_t v_i_boxed_879_; lean_object* v_res_880_; 
v_sz_boxed_878_ = lean_unbox_usize(v_sz_868_);
lean_dec(v_sz_868_);
v_i_boxed_879_ = lean_unbox_usize(v_i_869_);
lean_dec(v_i_869_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(v_as_867_, v_sz_boxed_878_, v_i_boxed_879_, v_b_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v_as_867_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_inst_881_, lean_object* v_a_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_inst_891_, lean_object* v_a_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_inst_891_, v_a_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec(v___y_893_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object* v_mvarId_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; lean_object* v_mctx_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = lean_st_ref_get(v___y_902_);
v_mctx_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc_ref(v_mctx_905_);
lean_dec(v___x_904_);
v___x_906_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_905_, v_mvarId_901_);
lean_dec_ref(v_mctx_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object* v_mvarId_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec(v_mvarId_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object* v_mvarId_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_912_, v___y_916_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object* v_mvarId_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec(v___y_922_);
lean_dec(v_mvarId_921_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object* v_a_930_, lean_object* v_as_931_, size_t v_sz_932_, size_t v_i_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_a_943_; uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_933_, v_sz_932_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_dec_ref(v_a_930_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v_b_934_);
return v___x_948_;
}
else
{
lean_object* v_array_949_; lean_object* v_start_950_; lean_object* v_stop_951_; uint8_t v___x_952_; 
v_array_949_ = lean_ctor_get(v_b_934_, 0);
v_start_950_ = lean_ctor_get(v_b_934_, 1);
v_stop_951_ = lean_ctor_get(v_b_934_, 2);
v___x_952_ = lean_nat_dec_lt(v_start_950_, v_stop_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec_ref(v_a_930_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_934_);
return v___x_953_;
}
else
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_977_; 
lean_inc(v_stop_951_);
lean_inc(v_start_950_);
lean_inc_ref(v_array_949_);
v_isSharedCheck_977_ = !lean_is_exclusive(v_b_934_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; 
v_unused_978_ = lean_ctor_get(v_b_934_, 2);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_b_934_, 1);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_b_934_, 0);
lean_dec(v_unused_980_);
v___x_955_ = v_b_934_;
v_isShared_956_ = v_isSharedCheck_977_;
goto v_resetjp_954_;
}
else
{
lean_dec(v_b_934_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_977_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_lctx_957_; lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v_lctx_957_ = lean_ctor_get(v_a_930_, 1);
v___x_958_ = lean_array_fget(v_array_949_, v_start_950_);
v_a_959_ = lean_array_uget_borrowed(v_as_931_, v_i_933_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_start_950_, v___x_960_);
lean_dec(v_start_950_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_961_);
v___x_963_ = v___x_955_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_array_949_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_stop_951_);
v___x_963_ = v_reuseFailAlloc_976_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; uint8_t v___x_965_; uint8_t v___x_966_; 
lean_inc_ref(v_lctx_957_);
v___x_964_ = l_Lean_LocalContext_getFVar_x21(v_lctx_957_, v_a_959_);
v___x_965_ = 0;
v___x_966_ = l_Lean_LocalDecl_isLet(v___x_964_, v___x_965_);
lean_dec_ref(v___x_964_);
if (v___x_966_ == 0)
{
lean_dec(v___x_958_);
v_a_943_ = v___x_963_;
goto v___jp_942_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v___x_958_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_dec_ref_known(v___x_967_, 1);
v_a_943_ = v___x_963_;
goto v___jp_942_;
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v___x_963_);
lean_dec_ref(v_a_930_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
}
}
v___jp_942_:
{
size_t v___x_944_; size_t v___x_945_; 
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_933_, v___x_944_);
v_i_933_ = v___x_945_;
v_b_934_ = v_a_943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object* v_a_981_, lean_object* v_as_982_, lean_object* v_sz_983_, lean_object* v_i_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_983_);
lean_dec(v_sz_983_);
v_i_boxed_994_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_981_, v_as_982_, v_sz_boxed_993_, v_i_boxed_994_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v_as_982_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object* v_as_996_, lean_object* v___y_997_){
_start:
{
if (lean_obj_tag(v_as_996_) == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
else
{
lean_object* v_head_1001_; lean_object* v_tail_1002_; lean_object* v___x_1003_; 
v_head_1001_ = lean_ctor_get(v_as_996_, 0);
lean_inc(v_head_1001_);
v_tail_1002_ = lean_ctor_get(v_as_996_, 1);
lean_inc(v_tail_1002_);
lean_dec_ref_known(v_as_996_, 2);
v___x_1003_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_head_1001_, v___y_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_dec_ref_known(v___x_1003_, 1);
v_as_996_ = v_tail_1002_;
goto _start;
}
else
{
lean_dec(v_tail_1002_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object* v_as_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1005_, v___y_1006_);
lean_dec(v___y_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object* v_mvarId_1009_, lean_object* v_args_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1018_; lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1075_; 
v___x_1018_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1009_, v_a_1014_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1075_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1075_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
if (lean_obj_tag(v_a_1019_) == 1)
{
lean_object* v_val_1023_; lean_object* v_fvars_1024_; lean_object* v_mvarIdPending_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
lean_del_object(v___x_1021_);
v_val_1023_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v_a_1019_, 1);
v_fvars_1024_ = lean_ctor_get(v_val_1023_, 0);
lean_inc_ref(v_fvars_1024_);
v_mvarIdPending_1025_ = lean_ctor_get(v_val_1023_, 1);
lean_inc(v_mvarIdPending_1025_);
lean_dec(v_val_1023_);
v___x_1026_ = lean_array_get_size(v_fvars_1024_);
v___x_1027_ = lean_array_get_size(v_args_1010_);
v___x_1028_ = lean_nat_dec_le(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec(v_mvarIdPending_1025_);
lean_dec_ref(v_fvars_1024_);
lean_dec_ref(v_args_1010_);
lean_inc(v_a_1011_);
v___x_1029_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_a_1011_, v_a_1014_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1029_, 0);
lean_dec(v_unused_1038_);
v___x_1031_ = v___x_1029_;
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1029_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_box(0);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
return v___x_1029_;
}
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_MVarId_getDecl(v_mvarIdPending_1025_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; size_t v_sz_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = l_Array_toSubarray___redArg(v_args_1010_, v___x_1041_, v___x_1027_);
v_sz_1043_ = lean_array_size(v_fvars_1024_);
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1040_, v_fvars_1024_, v_sz_1043_, v___x_1044_, v___x_1042_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec_ref(v_fvars_1024_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1045_, 0);
lean_dec(v_unused_1054_);
v___x_1047_ = v___x_1045_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_dec(v___x_1045_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1045_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1045_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_fvars_1024_);
lean_dec_ref(v_args_1010_);
v_a_1063_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1039_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1039_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_dec(v_a_1019_);
lean_dec_ref(v_args_1010_);
v___x_1071_ = lean_box(0);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1071_);
v___x_1073_ = v___x_1021_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object* v_mvarId_1076_, lean_object* v_args_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1076_, v_args_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec(v_mvarId_1076_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object* v_as_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1086_, v___y_1090_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object* v_as_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec(v___y_1096_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object* v_e_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = l_Lean_Expr_mvarId_x21(v_e_1106_);
v___x_1115_ = l_Lean_MVarId_findDecl_x3f___redArg(v___x_1114_, v_a_1110_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1146_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1146_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1146_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
if (lean_obj_tag(v_a_1116_) == 1)
{
lean_object* v_val_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1144_; 
v_val_1120_ = lean_ctor_get(v_a_1116_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_a_1116_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1122_ = v_a_1116_;
v_isShared_1123_ = v_isSharedCheck_1144_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_val_1120_);
lean_dec(v_a_1116_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1144_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint8_t v___x_1133_; 
v___x_1133_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1107_);
if (v___x_1133_ == 0)
{
lean_dec(v___x_1114_);
goto v___jp_1124_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_1135_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v___x_1114_, v___x_1134_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v___x_1114_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_dec_ref_known(v___x_1135_, 1);
goto v___jp_1124_;
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_del_object(v___x_1122_);
lean_dec(v_val_1120_);
lean_del_object(v___x_1118_);
lean_dec_ref(v_e_1106_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
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
v___jp_1124_:
{
lean_object* v_type_1125_; lean_object* v___x_1127_; 
v_type_1125_ = lean_ctor_get(v_val_1120_, 2);
lean_inc_ref(v_type_1125_);
lean_dec(v_val_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v_type_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_type_1125_);
v___x_1127_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_e_1106_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1128_);
v___x_1130_ = v___x_1118_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
else
{
lean_object* v___x_1145_; 
lean_del_object(v___x_1118_);
lean_dec(v_a_1116_);
lean_dec_ref(v_e_1106_);
v___x_1145_ = l_Lean_Meta_throwUnknownMVar___redArg(v___x_1114_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v___x_1114_);
lean_dec_ref(v_e_1106_);
v_a_1147_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1115_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1115_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object* v_e_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec(v_a_1156_);
return v_res_1163_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_instMonadEIO___redArg();
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object* v_msg_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_toApplicative_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1242_; 
v___x_1177_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0);
v___x_1178_ = l_StateRefT_x27_instMonad___redArg(v___x_1177_);
v_toApplicative_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1178_, 1);
lean_dec(v_unused_1243_);
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1242_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_toApplicative_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1242_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_toFunctor_1183_; lean_object* v_toSeq_1184_; lean_object* v_toSeqLeft_1185_; lean_object* v_toSeqRight_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1240_; 
v_toFunctor_1183_ = lean_ctor_get(v_toApplicative_1179_, 0);
v_toSeq_1184_ = lean_ctor_get(v_toApplicative_1179_, 2);
v_toSeqLeft_1185_ = lean_ctor_get(v_toApplicative_1179_, 3);
v_toSeqRight_1186_ = lean_ctor_get(v_toApplicative_1179_, 4);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_toApplicative_1179_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v_toApplicative_1179_, 1);
lean_dec(v_unused_1241_);
v___x_1188_ = v_toApplicative_1179_;
v_isShared_1189_ = v_isSharedCheck_1240_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_toSeqRight_1186_);
lean_inc(v_toSeqLeft_1185_);
lean_inc(v_toSeq_1184_);
lean_inc(v_toFunctor_1183_);
lean_dec(v_toApplicative_1179_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1240_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___x_1199_; 
v___f_1190_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1));
v___f_1191_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1183_);
v___f_1192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1192_, 0, v_toFunctor_1183_);
v___f_1193_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1193_, 0, v_toFunctor_1183_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___f_1192_);
lean_ctor_set(v___x_1194_, 1, v___f_1193_);
v___f_1195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1195_, 0, v_toSeqRight_1186_);
v___f_1196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1196_, 0, v_toSeqLeft_1185_);
v___f_1197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1197_, 0, v_toSeq_1184_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 4, v___f_1195_);
lean_ctor_set(v___x_1188_, 3, v___f_1196_);
lean_ctor_set(v___x_1188_, 2, v___f_1197_);
lean_ctor_set(v___x_1188_, 1, v___f_1190_);
lean_ctor_set(v___x_1188_, 0, v___x_1194_);
v___x_1199_ = v___x_1188_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___f_1190_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v___f_1197_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v___f_1196_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v___f_1195_);
v___x_1199_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___f_1191_);
lean_ctor_set(v___x_1181_, 0, v___x_1199_);
v___x_1201_ = v___x_1181_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___f_1191_);
v___x_1201_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; lean_object* v_toApplicative_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1236_; 
v___x_1202_ = l_StateRefT_x27_instMonad___redArg(v___x_1201_);
v_toApplicative_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1202_, 1);
lean_dec(v_unused_1237_);
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1236_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_toApplicative_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1236_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_toFunctor_1207_; lean_object* v_toSeq_1208_; lean_object* v_toSeqLeft_1209_; lean_object* v_toSeqRight_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1234_; 
v_toFunctor_1207_ = lean_ctor_get(v_toApplicative_1203_, 0);
v_toSeq_1208_ = lean_ctor_get(v_toApplicative_1203_, 2);
v_toSeqLeft_1209_ = lean_ctor_get(v_toApplicative_1203_, 3);
v_toSeqRight_1210_ = lean_ctor_get(v_toApplicative_1203_, 4);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_toApplicative_1203_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_toApplicative_1203_, 1);
lean_dec(v_unused_1235_);
v___x_1212_ = v_toApplicative_1203_;
v_isShared_1213_ = v_isSharedCheck_1234_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_toSeqRight_1210_);
lean_inc(v_toSeqLeft_1209_);
lean_inc(v_toSeq_1208_);
lean_inc(v_toFunctor_1207_);
lean_dec(v_toApplicative_1203_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1234_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___x_1223_; 
v___f_1214_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3));
v___f_1215_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1207_);
v___f_1216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1216_, 0, v_toFunctor_1207_);
v___f_1217_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1217_, 0, v_toFunctor_1207_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___f_1216_);
lean_ctor_set(v___x_1218_, 1, v___f_1217_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toSeqRight_1210_);
v___f_1220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1220_, 0, v_toSeqLeft_1209_);
v___f_1221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1221_, 0, v_toSeq_1208_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 4, v___f_1219_);
lean_ctor_set(v___x_1212_, 3, v___f_1220_);
lean_ctor_set(v___x_1212_, 2, v___f_1221_);
lean_ctor_set(v___x_1212_, 1, v___f_1214_);
lean_ctor_set(v___x_1212_, 0, v___x_1218_);
v___x_1223_ = v___x_1212_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___f_1214_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v___f_1221_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v___f_1220_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v___f_1219_);
v___x_1223_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___f_1215_);
lean_ctor_set(v___x_1205_, 0, v___x_1223_);
v___x_1225_ = v___x_1205_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___f_1215_);
v___x_1225_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1424__overap_1230_; lean_object* v___x_1231_; 
v___x_1226_ = l_StateRefT_x27_instMonad___redArg(v___x_1225_);
v___x_1227_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1228_ = l_instInhabitedOfMonad___redArg(v___x_1226_, v___x_1227_);
v___f_1229_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1229_, 0, v___x_1228_);
v___x_1424__overap_1230_ = lean_panic_fn_borrowed(v___f_1229_, v_msg_1169_);
lean_dec_ref(v___f_1229_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc(v___y_1170_);
v___x_1231_ = lean_apply_7(v___x_1424__overap_1230_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1231_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
return v_res_1252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
lean_ctor_set(v___x_1259_, 4, v___x_1257_);
lean_ctor_set(v___x_1259_, 5, v___x_1257_);
lean_ctor_set(v___x_1259_, 6, v___x_1257_);
lean_ctor_set(v___x_1259_, 7, v___x_1257_);
lean_ctor_set(v___x_1259_, 8, v___x_1257_);
lean_ctor_set(v___x_1259_, 9, v___x_1257_);
lean_ctor_set(v___x_1259_, 10, v___x_1257_);
lean_ctor_set(v___x_1259_, 11, v___x_1256_);
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(32u);
v___x_1261_ = lean_mk_empty_array_with_capacity(v___x_1260_);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1263_ = ((size_t)5ULL);
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_unsigned_to_nat(32u);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1265_);
v___x_1267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1268_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v___x_1266_);
lean_ctor_set(v___x_1268_, 2, v___x_1264_);
lean_ctor_set(v___x_1268_, 3, v___x_1264_);
lean_ctor_set_usize(v___x_1268_, 4, v___x_1263_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1269_ = lean_box(1);
v___x_1270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1270_);
lean_ctor_set(v___x_1272_, 2, v___x_1269_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_env_1300_; uint8_t v___x_1301_; 
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_st_ref_get(v___y_1296_);
v_env_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc_ref(v_env_1300_);
lean_dec(v___x_1299_);
v___x_1301_ = l_Lean_Name_isAnonymous(v_declHint_1295_);
if (v___x_1301_ == 0)
{
uint8_t v_isExporting_1302_; 
v_isExporting_1302_ = lean_ctor_get_uint8(v_env_1300_, sizeof(void*)*13);
if (v_isExporting_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec_ref(v_env_1300_);
lean_dec(v_declHint_1295_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_msg_1294_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
lean_inc_ref(v_env_1300_);
v___x_1304_ = l_Lean_Environment_setExporting(v_env_1300_, v___x_1301_);
lean_inc(v_declHint_1295_);
lean_inc_ref(v___x_1304_);
v___x_1305_ = l_Lean_Environment_contains(v___x_1304_, v_declHint_1295_, v_isExporting_1302_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_env_1300_);
lean_dec(v_declHint_1295_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_msg_1294_);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_c_1312_; lean_object* v___x_1313_; 
v___x_1307_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1309_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1304_);
v___x_1310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1304_);
lean_ctor_set(v___x_1310_, 1, v___x_1307_);
lean_ctor_set(v___x_1310_, 2, v___x_1308_);
lean_ctor_set(v___x_1310_, 3, v___x_1309_);
lean_inc(v_declHint_1295_);
v___x_1311_ = l_Lean_MessageData_ofConstName(v_declHint_1295_, v___x_1301_);
v_c_1312_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1312_, 0, v___x_1310_);
lean_ctor_set(v_c_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1304_, v_declHint_1295_);
lean_dec_ref(v___x_1304_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec_ref(v_env_1300_);
lean_dec(v_declHint_1295_);
v___x_1314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_c_1312_);
v___x_1316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = l_Lean_MessageData_note(v___x_1317_);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_msg_1294_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
else
{
lean_object* v_val_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1355_; 
v_val_1321_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1323_ = v___x_1313_;
v_isShared_1324_ = v_isSharedCheck_1355_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_val_1321_);
lean_dec(v___x_1313_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1355_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v_moduleNames_1326_; lean_object* v_mod_1327_; uint8_t v___x_1328_; 
v___x_1325_ = l_Lean_Environment_header(v_env_1300_);
lean_dec_ref(v_env_1300_);
v_moduleNames_1326_ = lean_ctor_get(v___x_1325_, 4);
lean_inc_ref(v_moduleNames_1326_);
lean_dec_ref(v___x_1325_);
v_mod_1327_ = lean_array_get(v___x_1298_, v_moduleNames_1326_, v_val_1321_);
lean_dec(v_val_1321_);
lean_dec_ref(v_moduleNames_1326_);
v___x_1328_ = l_Lean_isPrivateName(v_declHint_1295_);
lean_dec(v_declHint_1295_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1329_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v_c_1312_);
v___x_1331_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_MessageData_ofName(v_mod_1327_);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Lean_MessageData_note(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_msg_1294_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1338_);
v___x_1340_ = v___x_1323_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_c_1312_);
v___x_1344_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = l_Lean_MessageData_ofName(v_mod_1327_);
v___x_1347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_MessageData_note(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_msg_1294_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1351_);
v___x_1353_ = v___x_1323_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1356_; 
lean_dec_ref(v_env_1300_);
lean_dec(v_declHint_1295_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_msg_1294_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1357_, lean_object* v_declHint_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1357_, v_declHint_1358_, v___y_1359_);
lean_dec(v___y_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1362_, lean_object* v_declHint_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1381_; 
v___x_1371_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1362_, v_declHint_1363_, v___y_1369_);
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = l_Lean_unknownIdentifierMessageTag;
v___x_1377_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v_a_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1377_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1382_, lean_object* v_declHint_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1382_, v_declHint_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v_env_1399_; uint8_t v___x_1400_; lean_object* v_env_1401_; lean_object* v___x_1402_; lean_object* v_toCold_1403_; lean_object* v_mctx_1404_; lean_object* v_lctx_1405_; lean_object* v_options_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1398_ = lean_st_ref_get(v___y_1396_);
v_env_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc_ref(v_env_1399_);
lean_dec(v___x_1398_);
v___x_1400_ = 0;
v_env_1401_ = l_Lean_Environment_setRecordingDeps(v_env_1399_, v___x_1400_);
v___x_1402_ = lean_st_ref_get(v___y_1394_);
v_toCold_1403_ = lean_ctor_get(v___y_1395_, 0);
v_mctx_1404_ = lean_ctor_get(v___x_1402_, 0);
lean_inc_ref(v_mctx_1404_);
lean_dec(v___x_1402_);
v_lctx_1405_ = lean_ctor_get(v___y_1393_, 2);
v_options_1406_ = lean_ctor_get(v_toCold_1403_, 2);
lean_inc_ref(v_options_1406_);
lean_inc_ref(v_lctx_1405_);
v___x_1407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1407_, 0, v_env_1401_);
lean_ctor_set(v___x_1407_, 1, v_mctx_1404_);
lean_ctor_set(v___x_1407_, 2, v_lctx_1405_);
lean_ctor_set(v___x_1407_, 3, v_options_1406_);
v___x_1408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v_msgData_1392_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_ref_1423_; lean_object* v___x_1424_; lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
v_ref_1423_ = lean_ctor_get(v___y_1420_, 2);
v___x_1424_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_inc(v_ref_1423_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_ref_1423_);
lean_ctor_set(v___x_1429_, 1, v_a_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set_tag(v___x_1427_, 1);
lean_ctor_set(v___x_1427_, 0, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1441_, lean_object* v_msg_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_toCold_1450_; lean_object* v_currRecDepth_1451_; lean_object* v_ref_1452_; uint16_t v_optionFlags_1453_; uint8_t v_suppressElabErrors_1454_; uint8_t v_checkDeprecated_1455_; uint8_t v_isRecordingDeps_1456_; lean_object* v_ref_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_toCold_1450_ = lean_ctor_get(v___y_1447_, 0);
v_currRecDepth_1451_ = lean_ctor_get(v___y_1447_, 1);
v_ref_1452_ = lean_ctor_get(v___y_1447_, 2);
v_optionFlags_1453_ = lean_ctor_get_uint16(v___y_1447_, sizeof(void*)*3);
v_suppressElabErrors_1454_ = lean_ctor_get_uint8(v___y_1447_, sizeof(void*)*3 + 2);
v_checkDeprecated_1455_ = lean_ctor_get_uint8(v___y_1447_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1456_ = lean_ctor_get_uint8(v___y_1447_, sizeof(void*)*3 + 4);
v_ref_1457_ = l_Lean_replaceRef(v_ref_1441_, v_ref_1452_);
lean_inc(v_currRecDepth_1451_);
lean_inc_ref(v_toCold_1450_);
v___x_1458_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1458_, 0, v_toCold_1450_);
lean_ctor_set(v___x_1458_, 1, v_currRecDepth_1451_);
lean_ctor_set(v___x_1458_, 2, v_ref_1457_);
lean_ctor_set_uint16(v___x_1458_, sizeof(void*)*3, v_optionFlags_1453_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*3 + 2, v_suppressElabErrors_1454_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*3 + 3, v_checkDeprecated_1455_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*3 + 4, v_isRecordingDeps_1456_);
v___x_1459_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1442_, v___y_1445_, v___y_1446_, v___x_1458_, v___y_1448_);
lean_dec_ref_known(v___x_1458_, 3);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1460_, lean_object* v_msg_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1460_, v_msg_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v_ref_1460_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1470_, lean_object* v_msg_1471_, lean_object* v_declHint_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; lean_object* v_a_1481_; lean_object* v___x_1482_; 
v___x_1480_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1471_, v_declHint_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v___x_1480_);
v___x_1482_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1470_, v_a_1481_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1483_, lean_object* v_msg_1484_, lean_object* v_declHint_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1483_, v_msg_1484_, v_declHint_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v_ref_1483_);
return v_res_1493_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1496_ = l_Lean_stringToMessageData(v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1499_ = l_Lean_stringToMessageData(v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1500_, lean_object* v_constName_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1509_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1510_ = 0;
lean_inc(v_constName_1501_);
v___x_1511_ = l_Lean_MessageData_ofConstName(v_constName_1501_, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1509_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1500_, v___x_1514_, v_constName_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1516_, lean_object* v_constName_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1516_, v_constName_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec(v_ref_1516_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_ref_1534_; lean_object* v___x_1535_; 
v_ref_1534_ = lean_ctor_get(v___y_1531_, 2);
v___x_1535_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1534_, v_constName_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec(v___y_1537_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v_env_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_st_ref_get(v___y_1551_);
v_env_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc_ref(v_env_1554_);
lean_dec(v___x_1553_);
v___x_1555_ = 0;
lean_inc(v_constName_1545_);
v___x_1556_ = l_Lean_Environment_findConstVal_x3f(v_env_1554_, v_constName_1545_, v___x_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1557_;
}
else
{
lean_object* v_val_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_constName_1545_);
v_val_1558_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_val_1558_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 0);
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_val_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec(v___y_1567_);
return v_res_1574_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1579_ = lean_unsigned_to_nat(35u);
v___x_1580_ = lean_unsigned_to_nat(203u);
v___x_1581_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1582_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1583_ = l_mkPanicMessageWithDecl(v___x_1582_, v___x_1581_, v___x_1580_, v___x_1579_, v___x_1578_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
if (lean_obj_tag(v_e_1584_) == 4)
{
lean_object* v_declName_1592_; lean_object* v_us_1593_; lean_object* v___x_1594_; 
v_declName_1592_ = lean_ctor_get(v_e_1584_, 0);
v_us_1593_ = lean_ctor_get(v_e_1584_, 1);
lean_inc(v_declName_1592_);
v___x_1594_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1592_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v_levelParams_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v_levelParams_1596_ = lean_ctor_get(v_a_1595_, 1);
v___x_1597_ = l_List_lengthTR___redArg(v_levelParams_1596_);
v___x_1598_ = l_List_lengthTR___redArg(v_us_1593_);
v___x_1599_ = lean_nat_dec_eq(v___x_1597_, v___x_1598_);
lean_dec(v___x_1598_);
lean_dec(v___x_1597_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
lean_inc(v_us_1593_);
lean_inc(v_declName_1592_);
lean_dec(v_a_1595_);
lean_dec_ref_known(v_e_1584_, 2);
v___x_1600_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1592_, v_us_1593_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; 
lean_inc(v_us_1593_);
v___x_1601_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1595_, v_us_1593_, v___y_1590_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1611_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1602_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_e_1584_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1607_);
v___x_1609_ = v___x_1604_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref_known(v_e_1584_, 2);
v_a_1612_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1601_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1601_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref_known(v_e_1584_, 2);
v_a_1620_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1594_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1594_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec_ref(v_e_1584_);
v___x_1628_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1629_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1628_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec(v___y_1631_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v___y_1647_; lean_object* v___x_1648_; 
lean_inc_ref(v_e_1639_);
v___y_1647_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1647_, 0, v_e_1639_);
v___x_1648_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1639_, v___y_1647_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec(v_a_1650_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1658_, lean_object* v_constName_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1668_, lean_object* v_constName_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1668_, v_constName_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1678_, lean_object* v_ref_1679_, lean_object* v_constName_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1679_, v_constName_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1689_, lean_object* v_ref_1690_, lean_object* v_constName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1689_, v_ref_1690_, v_constName_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v_ref_1690_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1700_, lean_object* v_ref_1701_, lean_object* v_msg_1702_, lean_object* v_declHint_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1701_, v_msg_1702_, v_declHint_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_ref_1713_, lean_object* v_msg_1714_, lean_object* v_declHint_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1712_, v_ref_1713_, v_msg_1714_, v_declHint_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec(v_ref_1713_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1724_, lean_object* v_declHint_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1724_, v_declHint_1725_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1734_, lean_object* v_declHint_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1734_, v_declHint_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec(v___y_1736_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1744_, lean_object* v_ref_1745_, lean_object* v_msg_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1745_, v_msg_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_ref_1756_, lean_object* v_msg_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1755_, v_ref_1756_, v_msg_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec(v_ref_1756_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1766_, lean_object* v_msg_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1767_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1776_, lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1776_, v_msg_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec(v___y_1778_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
uint8_t v___x_1794_; 
v___x_1794_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1787_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_r_1786_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; 
lean_inc_ref(v_r_1786_);
v___x_1796_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1786_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1849_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1849_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1849_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_expr_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1847_; 
v_expr_1801_ = lean_ctor_get(v_r_1786_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_r_1786_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v_r_1786_, 1);
lean_dec(v_unused_1848_);
v___x_1803_ = v_r_1786_;
v_isShared_1804_ = v_isSharedCheck_1847_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_expr_1801_);
lean_dec(v_r_1786_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1847_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Lean_Expr_isSort(v_a_1797_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; 
lean_del_object(v___x_1799_);
lean_inc(v_a_1792_);
lean_inc_ref(v_a_1791_);
lean_inc(v_a_1790_);
lean_inc_ref(v_a_1789_);
v___x_1806_ = lean_whnf(v_a_1797_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1831_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1831_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1831_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
if (lean_obj_tag(v_a_1807_) == 3)
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1807_);
lean_inc_ref(v_expr_1801_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1811_);
v___x_1813_ = v___x_1803_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_expr_1801_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v_count_1815_; lean_object* v_results_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1828_; 
v___x_1814_ = lean_st_ref_take(v_a_1788_);
v_count_1815_ = lean_ctor_get(v___x_1814_, 0);
v_results_1816_ = lean_ctor_get(v___x_1814_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1818_ = v___x_1814_;
v_isShared_1819_ = v_isSharedCheck_1828_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_results_1816_);
lean_inc(v_count_1815_);
lean_dec(v___x_1814_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1828_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_inc_ref(v___x_1813_);
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1816_, v_expr_1801_, v___x_1813_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_count_1815_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_st_ref_put(v_a_1788_, v___x_1822_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1813_);
v___x_1825_ = v___x_1809_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1813_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
else
{
lean_object* v___x_1830_; 
lean_del_object(v___x_1809_);
lean_dec(v_a_1807_);
lean_del_object(v___x_1803_);
v___x_1830_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1801_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
return v___x_1830_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_del_object(v___x_1803_);
lean_dec_ref(v_expr_1801_);
v_a_1832_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1806_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1806_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1797_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1840_);
v___x_1842_ = v___x_1803_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_expr_1801_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1842_);
v___x_1844_ = v___x_1799_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
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
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v_r_1786_);
v_a_1850_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1796_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1796_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec(v_a_1859_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = l_Lean_instInhabitedExpr;
v___x_1869_ = lean_panic_fn_borrowed(v___x_1868_, v_msg_1867_);
return v___x_1869_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1874_ = lean_unsigned_to_nat(18u);
v___x_1875_ = lean_unsigned_to_nat(1906u);
v___x_1876_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1877_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1878_ = l_mkPanicMessageWithDecl(v___x_1877_, v___x_1876_, v___x_1875_, v___x_1874_, v___x_1873_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1879_, lean_object* v_f_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___y_1890_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1903_; lean_object* v_fType_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; uint8_t v___x_1964_; 
v___x_1964_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1882_);
if (v___x_1964_ == 0)
{
if (lean_obj_tag(v_e_1879_) == 5)
{
lean_object* v_expr_1965_; lean_object* v_expr_1966_; lean_object* v_fn_1967_; lean_object* v_arg_1968_; size_t v___x_1969_; size_t v___x_1970_; uint8_t v___x_1971_; 
v_expr_1965_ = lean_ctor_get(v_f_1880_, 0);
lean_inc_ref(v_expr_1965_);
lean_dec_ref(v_f_1880_);
v_expr_1966_ = lean_ctor_get(v_a_1881_, 0);
lean_inc_ref(v_expr_1966_);
lean_dec_ref(v_a_1881_);
v_fn_1967_ = lean_ctor_get(v_e_1879_, 0);
v_arg_1968_ = lean_ctor_get(v_e_1879_, 1);
v___x_1969_ = lean_ptr_addr(v_fn_1967_);
v___x_1970_ = lean_ptr_addr(v_expr_1965_);
v___x_1971_ = lean_usize_dec_eq(v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
lean_dec_ref_known(v_e_1879_, 2);
v___x_1972_ = l_Lean_Expr_app___override(v_expr_1965_, v_expr_1966_);
v___y_1890_ = v___x_1972_;
goto v___jp_1889_;
}
else
{
size_t v___x_1973_; size_t v___x_1974_; uint8_t v___x_1975_; 
v___x_1973_ = lean_ptr_addr(v_arg_1968_);
v___x_1974_ = lean_ptr_addr(v_expr_1966_);
v___x_1975_ = lean_usize_dec_eq(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
lean_dec_ref_known(v_e_1879_, 2);
v___x_1976_ = l_Lean_Expr_app___override(v_expr_1965_, v_expr_1966_);
v___y_1890_ = v___x_1976_;
goto v___jp_1889_;
}
else
{
lean_dec_ref(v_expr_1966_);
lean_dec_ref(v_expr_1965_);
v___y_1890_ = v_e_1879_;
goto v___jp_1889_;
}
}
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_f_1880_);
lean_dec_ref(v_e_1879_);
v___x_1977_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1978_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1977_);
v___y_1890_ = v___x_1978_;
goto v___jp_1889_;
}
}
else
{
lean_object* v___x_1979_; 
lean_inc_ref(v_f_1880_);
v___x_1979_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1880_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; uint8_t v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1981_ = l_Lean_Expr_isForall(v_a_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_inc(v_a_1887_);
lean_inc_ref(v_a_1886_);
lean_inc(v_a_1885_);
lean_inc_ref(v_a_1884_);
v___x_1982_ = lean_whnf(v_a_1980_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v_fType_1920_ = v_a_1983_;
v___y_1921_ = v_a_1883_;
v___y_1922_ = v_a_1884_;
v___y_1923_ = v_a_1885_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_f_1880_);
lean_dec_ref(v_e_1879_);
v_a_1984_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1982_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1982_);
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
v_fType_1920_ = v_a_1980_;
v___y_1921_ = v_a_1883_;
v___y_1922_ = v_a_1884_;
v___y_1923_ = v_a_1885_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_f_1880_);
lean_dec_ref(v_e_1879_);
v_a_1992_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1979_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1979_);
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
v___jp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___y_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
v___jp_1894_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1898_ = lean_expr_instantiate1(v___y_1895_, v___y_1896_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v___y_1895_);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___y_1897_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
v___jp_1902_:
{
if (lean_obj_tag(v_e_1879_) == 5)
{
lean_object* v_expr_1904_; lean_object* v_expr_1905_; lean_object* v_fn_1906_; lean_object* v_arg_1907_; size_t v___x_1908_; size_t v___x_1909_; uint8_t v___x_1910_; 
v_expr_1904_ = lean_ctor_get(v_f_1880_, 0);
lean_inc_ref(v_expr_1904_);
lean_dec_ref(v_f_1880_);
v_expr_1905_ = lean_ctor_get(v_a_1881_, 0);
lean_inc_ref(v_expr_1905_);
lean_dec_ref(v_a_1881_);
v_fn_1906_ = lean_ctor_get(v_e_1879_, 0);
v_arg_1907_ = lean_ctor_get(v_e_1879_, 1);
v___x_1908_ = lean_ptr_addr(v_fn_1906_);
v___x_1909_ = lean_ptr_addr(v_expr_1904_);
v___x_1910_ = lean_usize_dec_eq(v___x_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
lean_dec_ref_known(v_e_1879_, 2);
lean_inc_ref(v_expr_1905_);
v___x_1911_ = l_Lean_Expr_app___override(v_expr_1904_, v_expr_1905_);
v___y_1895_ = v___y_1903_;
v___y_1896_ = v_expr_1905_;
v___y_1897_ = v___x_1911_;
goto v___jp_1894_;
}
else
{
size_t v___x_1912_; size_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_ptr_addr(v_arg_1907_);
v___x_1913_ = lean_ptr_addr(v_expr_1905_);
v___x_1914_ = lean_usize_dec_eq(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref_known(v_e_1879_, 2);
lean_inc_ref(v_expr_1905_);
v___x_1915_ = l_Lean_Expr_app___override(v_expr_1904_, v_expr_1905_);
v___y_1895_ = v___y_1903_;
v___y_1896_ = v_expr_1905_;
v___y_1897_ = v___x_1915_;
goto v___jp_1894_;
}
else
{
lean_dec_ref(v_expr_1904_);
v___y_1895_ = v___y_1903_;
v___y_1896_ = v_expr_1905_;
v___y_1897_ = v_e_1879_;
goto v___jp_1894_;
}
}
}
else
{
lean_object* v_expr_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec_ref(v_f_1880_);
lean_dec_ref(v_e_1879_);
v_expr_1916_ = lean_ctor_get(v_a_1881_, 0);
lean_inc_ref(v_expr_1916_);
lean_dec_ref(v_a_1881_);
v___x_1917_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1918_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1917_);
v___y_1895_ = v___y_1903_;
v___y_1896_ = v_expr_1916_;
v___y_1897_ = v___x_1918_;
goto v___jp_1894_;
}
}
v___jp_1919_:
{
if (lean_obj_tag(v_fType_1920_) == 7)
{
lean_object* v_binderType_1926_; lean_object* v_body_1927_; lean_object* v___x_1928_; 
v_binderType_1926_ = lean_ctor_get(v_fType_1920_, 1);
lean_inc_ref(v_binderType_1926_);
v_body_1927_ = lean_ctor_get(v_fType_1920_, 2);
lean_inc_ref(v_body_1927_);
lean_dec_ref_known(v_fType_1920_, 3);
lean_inc_ref(v_a_1881_);
v___x_1928_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1881_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l_Lean_Meta_isExprDefEq(v_binderType_1926_, v_a_1929_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; uint8_t v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = lean_unbox(v_a_1931_);
lean_dec(v_a_1931_);
if (v___x_1932_ == 0)
{
lean_object* v_expr_1933_; lean_object* v_expr_1934_; lean_object* v___x_1935_; 
v_expr_1933_ = lean_ctor_get(v_f_1880_, 0);
v_expr_1934_ = lean_ctor_get(v_a_1881_, 0);
lean_inc_ref(v_expr_1934_);
lean_inc_ref(v_expr_1933_);
v___x_1935_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1933_, v_expr_1934_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v___y_1903_ = v_body_1927_;
goto v___jp_1902_;
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v_body_1927_);
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_f_1880_);
lean_dec_ref(v_e_1879_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
v___y_1903_ = v_body_1927_;
goto v___jp_1902_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_body_1927_);
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_f_1880_);
lean_dec_ref(v_e_1879_);
v_a_1944_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1930_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1930_);
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
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_body_1927_);
lean_dec_ref(v_binderType_1926_);
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_f_1880_);
lean_dec_ref(v_e_1879_);
v_a_1952_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1928_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1928_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_expr_1960_; lean_object* v_expr_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v_fType_1920_);
lean_dec_ref(v_e_1879_);
v_expr_1960_ = lean_ctor_get(v_f_1880_, 0);
lean_inc_ref(v_expr_1960_);
lean_dec_ref(v_f_1880_);
v_expr_1961_ = lean_ctor_get(v_a_1881_, 0);
lean_inc_ref(v_expr_1961_);
lean_dec_ref(v_a_1881_);
v___x_1962_ = l_Lean_Expr_app___override(v_expr_1960_, v_expr_1961_);
v___x_1963_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1962_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2000_, lean_object* v_f_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2000_, v_f_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec(v_a_2003_);
return v_res_2010_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2013_ = lean_unsigned_to_nat(37u);
v___x_2014_ = lean_unsigned_to_nat(345u);
v___x_2015_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2016_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2017_ = l_mkPanicMessageWithDecl(v___x_2016_, v___x_2015_, v___x_2014_, v___x_2013_, v___x_2012_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2018_, lean_object* v_i_2019_, lean_object* v_a_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_zero_2028_; uint8_t v_isZero_2029_; 
v_zero_2028_ = lean_unsigned_to_nat(0u);
v_isZero_2029_ = lean_nat_dec_eq(v_i_2019_, v_zero_2028_);
if (v_isZero_2029_ == 1)
{
lean_object* v___x_2030_; 
lean_dec(v_i_2019_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_a_2020_);
return v___x_2030_;
}
else
{
lean_object* v_one_2031_; lean_object* v_n_2032_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2043_; lean_object* v___x_2046_; 
v_one_2031_ = lean_unsigned_to_nat(1u);
v_n_2032_ = lean_nat_sub(v_i_2019_, v_one_2031_);
lean_dec(v_i_2019_);
v___x_2046_ = lean_array_fget_borrowed(v_fvars_2018_, v_n_2032_);
if (lean_obj_tag(v___x_2046_) == 1)
{
lean_object* v_fvarId_2047_; lean_object* v___x_2048_; 
v_fvarId_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_fvarId_2047_);
v___x_2048_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2047_, v___y_2023_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
if (lean_obj_tag(v_a_2049_) == 1)
{
lean_object* v_val_2050_; 
v_val_2050_ = lean_ctor_get(v_a_2049_, 0);
lean_inc(v_val_2050_);
lean_dec_ref_known(v_a_2049_, 1);
if (lean_obj_tag(v_val_2050_) == 0)
{
lean_object* v_userName_2051_; lean_object* v_type_2052_; uint8_t v_bi_2053_; lean_object* v_expr_2054_; lean_object* v_type_x3f_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2076_; 
v_userName_2051_ = lean_ctor_get(v_val_2050_, 2);
lean_inc(v_userName_2051_);
v_type_2052_ = lean_ctor_get(v_val_2050_, 3);
lean_inc_ref(v_type_2052_);
v_bi_2053_ = lean_ctor_get_uint8(v_val_2050_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2050_, 4);
v_expr_2054_ = lean_ctor_get(v_a_2020_, 0);
v_type_x3f_2055_ = lean_ctor_get(v_a_2020_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2057_ = v_a_2020_;
v_isShared_2058_ = v_isSharedCheck_2076_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_type_x3f_2055_);
lean_inc(v_expr_2054_);
lean_dec(v_a_2020_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2076_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___y_2062_; 
v___x_2059_ = lean_expr_abstract_range(v_type_2052_, v_n_2032_, v_fvars_2018_);
lean_dec_ref(v_type_2052_);
lean_inc_ref(v___x_2059_);
lean_inc(v_userName_2051_);
v___x_2060_ = l_Lean_Expr_lam___override(v_userName_2051_, v___x_2059_, v_expr_2054_, v_bi_2053_);
if (lean_obj_tag(v_type_x3f_2055_) == 0)
{
lean_dec_ref(v___x_2059_);
lean_dec(v_userName_2051_);
v___y_2062_ = v_type_x3f_2055_;
goto v___jp_2061_;
}
else
{
lean_object* v_val_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_val_2067_ = lean_ctor_get(v_type_x3f_2055_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_type_x3f_2055_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v_type_x3f_2055_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_val_2067_);
lean_dec(v_type_x3f_2055_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = l_Lean_Expr_forallE___override(v_userName_2051_, v___x_2059_, v_val_2067_, v_bi_2053_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
v___y_2062_ = v___x_2073_;
goto v___jp_2061_;
}
}
}
v___jp_2061_:
{
lean_object* v___x_2064_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___y_2062_);
lean_ctor_set(v___x_2057_, 0, v___x_2060_);
v___x_2064_ = v___x_2057_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___y_2062_);
v___x_2064_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
v_i_2019_ = v_n_2032_;
v_a_2020_ = v___x_2064_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2077_; lean_object* v_type_2078_; lean_object* v_value_2079_; uint8_t v_nondep_2080_; uint8_t v_nondep_2082_; lean_object* v___x_2092_; 
v_userName_2077_ = lean_ctor_get(v_val_2050_, 2);
lean_inc(v_userName_2077_);
v_type_2078_ = lean_ctor_get(v_val_2050_, 3);
lean_inc_ref(v_type_2078_);
v_value_2079_ = lean_ctor_get(v_val_2050_, 4);
lean_inc_ref(v_value_2079_);
v_nondep_2080_ = lean_ctor_get_uint8(v_val_2050_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2050_, 5);
v___x_2092_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2024_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; uint8_t v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = 1;
if (v_nondep_2080_ == 0)
{
uint8_t v___x_2095_; 
v___x_2095_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2047_, v_a_2093_);
lean_dec(v_a_2093_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2022_);
lean_dec_ref(v___x_2096_);
v_nondep_2082_ = v___x_2094_;
goto v___jp_2081_;
}
else
{
v_nondep_2082_ = v_nondep_2080_;
goto v___jp_2081_;
}
}
else
{
lean_dec(v_a_2093_);
v_nondep_2082_ = v___x_2094_;
goto v___jp_2081_;
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_value_2079_);
lean_dec_ref(v_type_2078_);
lean_dec(v_userName_2077_);
lean_dec(v_n_2032_);
lean_dec_ref(v_a_2020_);
v_a_2097_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2092_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2092_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
v___jp_2081_:
{
lean_object* v_expr_2083_; lean_object* v_type_x3f_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_expr_2083_ = lean_ctor_get(v_a_2020_, 0);
lean_inc_ref(v_expr_2083_);
v_type_x3f_2084_ = lean_ctor_get(v_a_2020_, 1);
lean_inc(v_type_x3f_2084_);
lean_dec_ref(v_a_2020_);
v___x_2085_ = lean_expr_abstract_range(v_type_2078_, v_n_2032_, v_fvars_2018_);
lean_dec_ref(v_type_2078_);
v___x_2086_ = lean_expr_abstract_range(v_value_2079_, v_n_2032_, v_fvars_2018_);
lean_dec_ref(v_value_2079_);
lean_inc_ref(v___x_2086_);
lean_inc_ref(v___x_2085_);
lean_inc(v_userName_2077_);
v___x_2087_ = l_Lean_Expr_letE___override(v_userName_2077_, v___x_2085_, v___x_2086_, v_expr_2083_, v_nondep_2082_);
if (lean_obj_tag(v_type_x3f_2084_) == 0)
{
lean_dec_ref(v___x_2086_);
lean_dec_ref(v___x_2085_);
lean_dec(v_userName_2077_);
v___y_2034_ = v___x_2087_;
v___y_2035_ = v_type_x3f_2084_;
goto v___jp_2033_;
}
else
{
lean_object* v_val_2088_; uint8_t v___x_2089_; 
v_val_2088_ = lean_ctor_get(v_type_x3f_2084_, 0);
lean_inc(v_val_2088_);
lean_dec_ref_known(v_type_x3f_2084_, 1);
v___x_2089_ = lean_expr_has_loose_bvar(v_val_2088_, v_zero_2028_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec_ref(v___x_2086_);
lean_dec_ref(v___x_2085_);
lean_dec(v_userName_2077_);
v___x_2090_ = lean_expr_lower_loose_bvars(v_val_2088_, v_one_2031_, v_one_2031_);
lean_dec(v_val_2088_);
v___y_2039_ = v___x_2087_;
v___y_2040_ = v___x_2090_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Expr_letE___override(v_userName_2077_, v___x_2085_, v___x_2086_, v_val_2088_, v_nondep_2082_);
v___y_2039_ = v___x_2087_;
v___y_2040_ = v___x_2091_;
goto v___jp_2038_;
}
}
}
}
}
else
{
lean_object* v___x_2105_; 
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2020_);
lean_inc(v_fvarId_2047_);
v___x_2105_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2047_, v___y_2025_, v___y_2026_);
v___y_2043_ = v___x_2105_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_n_2032_);
lean_dec_ref(v_a_2020_);
v_a_2106_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2048_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2048_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v_a_2020_);
v___x_2114_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2115_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2114_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
v___y_2043_ = v___x_2115_;
goto v___jp_2042_;
}
v___jp_2033_:
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___y_2034_);
lean_ctor_set(v___x_2036_, 1, v___y_2035_);
v_i_2019_ = v_n_2032_;
v_a_2020_ = v___x_2036_;
goto _start;
}
v___jp_2038_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___y_2040_);
v___y_2034_ = v___y_2039_;
v___y_2035_ = v___x_2041_;
goto v___jp_2033_;
}
v___jp_2042_:
{
if (lean_obj_tag(v___y_2043_) == 0)
{
lean_object* v_a_2044_; 
v_a_2044_ = lean_ctor_get(v___y_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___y_2043_, 1);
v_i_2019_ = v_n_2032_;
v_a_2020_ = v_a_2044_;
goto _start;
}
else
{
lean_dec(v_n_2032_);
return v___y_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2116_, lean_object* v_i_2117_, lean_object* v_a_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2116_, v_i_2117_, v_a_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v_fvars_2116_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
if (lean_obj_tag(v_a_2127_) == 0)
{
lean_object* v___x_2129_; 
v___x_2129_ = l_List_reverse___redArg(v_a_2128_);
return v___x_2129_;
}
else
{
lean_object* v_head_2130_; lean_object* v_tail_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2140_; 
v_head_2130_ = lean_ctor_get(v_a_2127_, 0);
v_tail_2131_ = lean_ctor_get(v_a_2127_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2133_ = v_a_2127_;
v_isShared_2134_ = v_isSharedCheck_2140_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_tail_2131_);
lean_inc(v_head_2130_);
lean_dec(v_a_2127_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2140_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = l_Lean_MessageData_ofExpr(v_head_2130_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v_a_2128_);
lean_ctor_set(v___x_2133_, 0, v___x_2135_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_a_2128_);
v___x_2137_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
v_a_2127_ = v_tail_2131_;
v_a_2128_ = v___x_2137_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2141_; double v___x_2142_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_float_of_nat(v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2146_, lean_object* v_msg_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_ref_2153_; lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2200_; 
v_ref_2153_ = lean_ctor_get(v___y_2150_, 2);
v___x_2154_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2200_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2200_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v_traceState_2160_; lean_object* v_env_2161_; lean_object* v_nextMacroScope_2162_; lean_object* v_ngen_2163_; lean_object* v_auxDeclNGen_2164_; lean_object* v_cache_2165_; lean_object* v_recordedDeps_2166_; lean_object* v_messages_2167_; lean_object* v_infoState_2168_; lean_object* v_snapshotTasks_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2199_; 
v___x_2159_ = lean_st_ref_take(v___y_2151_);
v_traceState_2160_ = lean_ctor_get(v___x_2159_, 4);
v_env_2161_ = lean_ctor_get(v___x_2159_, 0);
v_nextMacroScope_2162_ = lean_ctor_get(v___x_2159_, 1);
v_ngen_2163_ = lean_ctor_get(v___x_2159_, 2);
v_auxDeclNGen_2164_ = lean_ctor_get(v___x_2159_, 3);
v_cache_2165_ = lean_ctor_get(v___x_2159_, 5);
v_recordedDeps_2166_ = lean_ctor_get(v___x_2159_, 6);
v_messages_2167_ = lean_ctor_get(v___x_2159_, 7);
v_infoState_2168_ = lean_ctor_get(v___x_2159_, 8);
v_snapshotTasks_2169_ = lean_ctor_get(v___x_2159_, 9);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2171_ = v___x_2159_;
v_isShared_2172_ = v_isSharedCheck_2199_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_snapshotTasks_2169_);
lean_inc(v_infoState_2168_);
lean_inc(v_messages_2167_);
lean_inc(v_recordedDeps_2166_);
lean_inc(v_cache_2165_);
lean_inc(v_traceState_2160_);
lean_inc(v_auxDeclNGen_2164_);
lean_inc(v_ngen_2163_);
lean_inc(v_nextMacroScope_2162_);
lean_inc(v_env_2161_);
lean_dec(v___x_2159_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2199_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
uint64_t v_tid_2173_; lean_object* v_traces_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2198_; 
v_tid_2173_ = lean_ctor_get_uint64(v_traceState_2160_, sizeof(void*)*1);
v_traces_2174_ = lean_ctor_get(v_traceState_2160_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_traceState_2160_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2176_ = v_traceState_2160_;
v_isShared_2177_ = v_isSharedCheck_2198_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_traces_2174_);
lean_dec(v_traceState_2160_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2198_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; double v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2181_ = 0;
v___x_2182_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2183_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2183_, 0, v_cls_2146_);
lean_ctor_set(v___x_2183_, 1, v___x_2179_);
lean_ctor_set(v___x_2183_, 2, v___x_2182_);
lean_ctor_set_float(v___x_2183_, sizeof(void*)*3, v___x_2180_);
lean_ctor_set_float(v___x_2183_, sizeof(void*)*3 + 8, v___x_2180_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*3 + 16, v___x_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2185_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v_a_2155_);
lean_ctor_set(v___x_2185_, 2, v___x_2184_);
lean_inc(v_ref_2153_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_ref_2153_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_PersistentArray_push___redArg(v_traces_2174_, v___x_2186_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2187_);
v___x_2189_ = v___x_2176_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2187_);
lean_ctor_set_uint64(v_reuseFailAlloc_2197_, sizeof(void*)*1, v_tid_2173_);
v___x_2189_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 4, v___x_2189_);
v___x_2191_ = v___x_2171_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_env_2161_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_nextMacroScope_2162_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_ngen_2163_);
lean_ctor_set(v_reuseFailAlloc_2196_, 3, v_auxDeclNGen_2164_);
lean_ctor_set(v_reuseFailAlloc_2196_, 4, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2196_, 5, v_cache_2165_);
lean_ctor_set(v_reuseFailAlloc_2196_, 6, v_recordedDeps_2166_);
lean_ctor_set(v_reuseFailAlloc_2196_, 7, v_messages_2167_);
lean_ctor_set(v_reuseFailAlloc_2196_, 8, v_infoState_2168_);
lean_ctor_set(v_reuseFailAlloc_2196_, 9, v_snapshotTasks_2169_);
v___x_2191_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = lean_st_ref_put(v___y_2151_, v___x_2191_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2178_);
v___x_2194_ = v___x_2157_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2178_);
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
lean_ctor_set(v___x_2254_, 0, v___y_2247_);
lean_ctor_set(v___x_2254_, 1, v___y_2253_);
v___x_2255_ = lean_array_get_size(v_fvars_2236_);
v___x_2256_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2236_, v___x_2255_, v___x_2254_, v___y_2246_, v___y_2248_, v___y_2250_, v___y_2252_, v___y_2249_, v___y_2251_);
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
v___y_2246_ = v___y_2258_;
v___y_2247_ = v___x_2266_;
v___y_2248_ = v___y_2259_;
v___y_2249_ = v___y_2262_;
v___y_2250_ = v___y_2260_;
v___y_2251_ = v___y_2263_;
v___y_2252_ = v___y_2261_;
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
v___y_2246_ = v___y_2258_;
v___y_2247_ = v___x_2266_;
v___y_2248_ = v___y_2259_;
v___y_2249_ = v___y_2262_;
v___y_2250_ = v___y_2260_;
v___y_2251_ = v___y_2263_;
v___y_2252_ = v___y_2261_;
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
uint8_t v_a_19061__boxed_2589_; lean_object* v_res_2590_; 
v_a_19061__boxed_2589_ = lean_unbox(v_a_2576_);
v_res_2590_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2572_, v_fst_2573_, v_struct_2574_, v_structName_2575_, v_a_19061__boxed_2589_, v___f_2577_, v_snd_2578_, v_____r_2579_, v_ctorType_2580_, v_j_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
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
uint8_t v_a_19218__boxed_2669_; lean_object* v_res_2670_; 
v_a_19218__boxed_2669_ = lean_unbox(v_a_2657_);
v_res_2670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2654_, v_struct_2655_, v_structName_2656_, v_a_19218__boxed_2669_, v_idx_2658_, v_a_2659_, v_a_2660_, v_b_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
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
v___x_2675_ = lean_unsigned_to_nat(1955u);
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
lean_dec(v_snd_2777_);
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
uint8_t v_a_19742__boxed_2933_; lean_object* v_res_2934_; 
v_a_19742__boxed_2933_ = lean_unbox(v_a_2918_);
v_res_2934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2915_, v_struct_2916_, v_structName_2917_, v_a_19742__boxed_2933_, v_idx_2919_, v_a_2920_, v_inst_2921_, v_R_2922_, v_a_2923_, v_b_2924_, v_c_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
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
lean_object* v_toCold_3158_; lean_object* v_currRecDepth_3159_; lean_object* v_ref_3160_; uint16_t v_optionFlags_3161_; uint8_t v_suppressElabErrors_3162_; uint8_t v_checkDeprecated_3163_; uint8_t v_isRecordingDeps_3164_; lean_object* v_ref_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v_traceState_3168_; lean_object* v_traces_3169_; lean_object* v___x_3170_; size_t v_sz_3171_; size_t v___x_3172_; lean_object* v___x_3173_; lean_object* v_msg_3174_; lean_object* v___x_3175_; lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3214_; 
v_toCold_3158_ = lean_ctor_get(v___y_3155_, 0);
v_currRecDepth_3159_ = lean_ctor_get(v___y_3155_, 1);
v_ref_3160_ = lean_ctor_get(v___y_3155_, 2);
v_optionFlags_3161_ = lean_ctor_get_uint16(v___y_3155_, sizeof(void*)*3);
v_suppressElabErrors_3162_ = lean_ctor_get_uint8(v___y_3155_, sizeof(void*)*3 + 2);
v_checkDeprecated_3163_ = lean_ctor_get_uint8(v___y_3155_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3164_ = lean_ctor_get_uint8(v___y_3155_, sizeof(void*)*3 + 4);
v_ref_3165_ = l_Lean_replaceRef(v_ref_3151_, v_ref_3160_);
lean_inc(v_currRecDepth_3159_);
lean_inc_ref(v_toCold_3158_);
v___x_3166_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3166_, 0, v_toCold_3158_);
lean_ctor_set(v___x_3166_, 1, v_currRecDepth_3159_);
lean_ctor_set(v___x_3166_, 2, v_ref_3165_);
lean_ctor_set_uint16(v___x_3166_, sizeof(void*)*3, v_optionFlags_3161_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*3 + 2, v_suppressElabErrors_3162_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*3 + 3, v_checkDeprecated_3163_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*3 + 4, v_isRecordingDeps_3164_);
v___x_3167_ = lean_st_ref_get(v___y_3156_);
v_traceState_3168_ = lean_ctor_get(v___x_3167_, 4);
lean_inc_ref(v_traceState_3168_);
lean_dec(v___x_3167_);
v_traces_3169_ = lean_ctor_get(v_traceState_3168_, 0);
lean_inc_ref(v_traces_3169_);
lean_dec_ref(v_traceState_3168_);
v___x_3170_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3169_);
lean_dec_ref(v_traces_3169_);
v_sz_3171_ = lean_array_size(v___x_3170_);
v___x_3172_ = ((size_t)0ULL);
v___x_3173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3171_, v___x_3172_, v___x_3170_);
v_msg_3174_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3174_, 0, v_data_3150_);
lean_ctor_set(v_msg_3174_, 1, v_msg_3152_);
lean_ctor_set(v_msg_3174_, 2, v___x_3173_);
v___x_3175_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3174_, v___y_3153_, v___y_3154_, v___x_3166_, v___y_3156_);
lean_dec_ref_known(v___x_3166_, 3);
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3214_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3214_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v_traceState_3181_; lean_object* v_env_3182_; lean_object* v_nextMacroScope_3183_; lean_object* v_ngen_3184_; lean_object* v_auxDeclNGen_3185_; lean_object* v_cache_3186_; lean_object* v_recordedDeps_3187_; lean_object* v_messages_3188_; lean_object* v_infoState_3189_; lean_object* v_snapshotTasks_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3213_; 
v___x_3180_ = lean_st_ref_take(v___y_3156_);
v_traceState_3181_ = lean_ctor_get(v___x_3180_, 4);
v_env_3182_ = lean_ctor_get(v___x_3180_, 0);
v_nextMacroScope_3183_ = lean_ctor_get(v___x_3180_, 1);
v_ngen_3184_ = lean_ctor_get(v___x_3180_, 2);
v_auxDeclNGen_3185_ = lean_ctor_get(v___x_3180_, 3);
v_cache_3186_ = lean_ctor_get(v___x_3180_, 5);
v_recordedDeps_3187_ = lean_ctor_get(v___x_3180_, 6);
v_messages_3188_ = lean_ctor_get(v___x_3180_, 7);
v_infoState_3189_ = lean_ctor_get(v___x_3180_, 8);
v_snapshotTasks_3190_ = lean_ctor_get(v___x_3180_, 9);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3192_ = v___x_3180_;
v_isShared_3193_ = v_isSharedCheck_3213_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_snapshotTasks_3190_);
lean_inc(v_infoState_3189_);
lean_inc(v_messages_3188_);
lean_inc(v_recordedDeps_3187_);
lean_inc(v_cache_3186_);
lean_inc(v_traceState_3181_);
lean_inc(v_auxDeclNGen_3185_);
lean_inc(v_ngen_3184_);
lean_inc(v_nextMacroScope_3183_);
lean_inc(v_env_3182_);
lean_dec(v___x_3180_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3213_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
uint64_t v_tid_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3211_; 
v_tid_3194_ = lean_ctor_get_uint64(v_traceState_3181_, sizeof(void*)*1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_traceState_3181_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v_traceState_3181_, 0);
lean_dec(v_unused_3212_);
v___x_3196_ = v_traceState_3181_;
v_isShared_3197_ = v_isSharedCheck_3211_;
goto v_resetjp_3195_;
}
else
{
lean_dec(v_traceState_3181_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3211_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_ref_3151_);
lean_ctor_set(v___x_3199_, 1, v_a_3176_);
v___x_3200_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3149_, v___x_3199_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3200_);
v___x_3202_ = v___x_3196_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3200_);
lean_ctor_set_uint64(v_reuseFailAlloc_3210_, sizeof(void*)*1, v_tid_3194_);
v___x_3202_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 4, v___x_3202_);
v___x_3204_ = v___x_3192_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_env_3182_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_nextMacroScope_3183_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v_ngen_3184_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v_auxDeclNGen_3185_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3209_, 5, v_cache_3186_);
lean_ctor_set(v_reuseFailAlloc_3209_, 6, v_recordedDeps_3187_);
lean_ctor_set(v_reuseFailAlloc_3209_, 7, v_messages_3188_);
lean_ctor_set(v_reuseFailAlloc_3209_, 8, v_infoState_3189_);
lean_ctor_set(v_reuseFailAlloc_3209_, 9, v_snapshotTasks_3190_);
v___x_3204_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3205_ = lean_st_ref_put(v___y_3156_, v___x_3204_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3198_);
v___x_3207_ = v___x_3178_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3198_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3215_, lean_object* v_data_3216_, lean_object* v_ref_3217_, lean_object* v_msg_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3215_, v_data_3216_, v_ref_3217_, v_msg_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
return v_res_3224_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3227_ = l_Lean_stringToMessageData(v___x_3226_);
return v___x_3227_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3228_; double v___x_3229_; 
v___x_3228_ = lean_unsigned_to_nat(1000u);
v___x_3229_ = lean_float_of_nat(v___x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3230_, uint8_t v_collapsed_3231_, lean_object* v_tag_3232_, lean_object* v_opts_3233_, uint8_t v_clsEnabled_3234_, lean_object* v_oldTraces_3235_, lean_object* v_msg_3236_, lean_object* v_resStartStop_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_fst_3245_; lean_object* v_snd_3246_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v_data_3250_; lean_object* v_fst_3261_; lean_object* v_snd_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; lean_object* v___y_3266_; lean_object* v_a_3267_; uint8_t v___y_3282_; double v___y_3314_; 
v_fst_3245_ = lean_ctor_get(v_resStartStop_3237_, 0);
lean_inc(v_fst_3245_);
v_snd_3246_ = lean_ctor_get(v_resStartStop_3237_, 1);
lean_inc(v_snd_3246_);
lean_dec_ref(v_resStartStop_3237_);
v_fst_3261_ = lean_ctor_get(v_snd_3246_, 0);
lean_inc(v_fst_3261_);
v_snd_3262_ = lean_ctor_get(v_snd_3246_, 1);
lean_inc(v_snd_3262_);
lean_dec(v_snd_3246_);
v___x_3263_ = l_Lean_trace_profiler;
v___x_3264_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3233_, v___x_3263_);
if (v___x_3264_ == 0)
{
v___y_3282_ = v___x_3264_;
goto v___jp_3281_;
}
else
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3320_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3233_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; double v___x_3323_; double v___x_3324_; double v___x_3325_; 
v___x_3321_ = l_Lean_trace_profiler_threshold;
v___x_3322_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3233_, v___x_3321_);
v___x_3323_ = lean_float_of_nat(v___x_3322_);
v___x_3324_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3325_ = lean_float_div(v___x_3323_, v___x_3324_);
v___y_3314_ = v___x_3325_;
goto v___jp_3313_;
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; double v___x_3328_; 
v___x_3326_ = l_Lean_trace_profiler_threshold;
v___x_3327_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3233_, v___x_3326_);
v___x_3328_ = lean_float_of_nat(v___x_3327_);
v___y_3314_ = v___x_3328_;
goto v___jp_3313_;
}
}
v___jp_3247_:
{
lean_object* v___x_3251_; 
lean_inc(v___y_3248_);
v___x_3251_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3235_, v_data_3250_, v___y_3248_, v___y_3249_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v___x_3252_; 
lean_dec_ref_known(v___x_3251_, 1);
v___x_3252_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3245_);
return v___x_3252_;
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v_fst_3245_);
v_a_3253_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3251_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3251_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
v___jp_3265_:
{
uint8_t v_result_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; double v___x_3271_; lean_object* v_data_3272_; 
v_result_3268_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3245_);
v___x_3269_ = lean_box(v_result_3268_);
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
v___x_3271_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3232_);
lean_inc_ref(v___x_3270_);
lean_inc(v_cls_3230_);
v_data_3272_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3272_, 0, v_cls_3230_);
lean_ctor_set(v_data_3272_, 1, v___x_3270_);
lean_ctor_set(v_data_3272_, 2, v_tag_3232_);
lean_ctor_set_float(v_data_3272_, sizeof(void*)*3, v___x_3271_);
lean_ctor_set_float(v_data_3272_, sizeof(void*)*3 + 8, v___x_3271_);
lean_ctor_set_uint8(v_data_3272_, sizeof(void*)*3 + 16, v_collapsed_3231_);
if (v___x_3264_ == 0)
{
lean_dec_ref_known(v___x_3270_, 1);
lean_dec(v_snd_3262_);
lean_dec(v_fst_3261_);
lean_dec_ref(v_tag_3232_);
lean_dec(v_cls_3230_);
v___y_3248_ = v___y_3266_;
v___y_3249_ = v_a_3267_;
v_data_3250_ = v_data_3272_;
goto v___jp_3247_;
}
else
{
lean_object* v_data_3273_; double v___x_3274_; double v___x_3275_; 
lean_dec_ref_known(v_data_3272_, 3);
v_data_3273_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3273_, 0, v_cls_3230_);
lean_ctor_set(v_data_3273_, 1, v___x_3270_);
lean_ctor_set(v_data_3273_, 2, v_tag_3232_);
v___x_3274_ = lean_unbox_float(v_fst_3261_);
lean_dec(v_fst_3261_);
lean_ctor_set_float(v_data_3273_, sizeof(void*)*3, v___x_3274_);
v___x_3275_ = lean_unbox_float(v_snd_3262_);
lean_dec(v_snd_3262_);
lean_ctor_set_float(v_data_3273_, sizeof(void*)*3 + 8, v___x_3275_);
lean_ctor_set_uint8(v_data_3273_, sizeof(void*)*3 + 16, v_collapsed_3231_);
v___y_3248_ = v___y_3266_;
v___y_3249_ = v_a_3267_;
v_data_3250_ = v_data_3273_;
goto v___jp_3247_;
}
}
v___jp_3276_:
{
lean_object* v_ref_3277_; lean_object* v___x_3278_; 
v_ref_3277_ = lean_ctor_get(v___y_3242_, 2);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
lean_inc(v___y_3239_);
lean_inc(v___y_3238_);
lean_inc(v_fst_3245_);
v___x_3278_ = lean_apply_8(v_msg_3236_, v_fst_3245_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, lean_box(0));
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___y_3266_ = v_ref_3277_;
v_a_3267_ = v_a_3279_;
goto v___jp_3265_;
}
else
{
lean_object* v___x_3280_; 
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3266_ = v_ref_3277_;
v_a_3267_ = v___x_3280_;
goto v___jp_3265_;
}
}
v___jp_3281_:
{
if (v_clsEnabled_3234_ == 0)
{
if (v___y_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v_traceState_3284_; lean_object* v_env_3285_; lean_object* v_nextMacroScope_3286_; lean_object* v_ngen_3287_; lean_object* v_auxDeclNGen_3288_; lean_object* v_cache_3289_; lean_object* v_recordedDeps_3290_; lean_object* v_messages_3291_; lean_object* v_infoState_3292_; lean_object* v_snapshotTasks_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3312_; 
lean_dec(v_snd_3262_);
lean_dec(v_fst_3261_);
lean_dec_ref(v_msg_3236_);
lean_dec_ref(v_tag_3232_);
lean_dec(v_cls_3230_);
v___x_3283_ = lean_st_ref_take(v___y_3243_);
v_traceState_3284_ = lean_ctor_get(v___x_3283_, 4);
v_env_3285_ = lean_ctor_get(v___x_3283_, 0);
v_nextMacroScope_3286_ = lean_ctor_get(v___x_3283_, 1);
v_ngen_3287_ = lean_ctor_get(v___x_3283_, 2);
v_auxDeclNGen_3288_ = lean_ctor_get(v___x_3283_, 3);
v_cache_3289_ = lean_ctor_get(v___x_3283_, 5);
v_recordedDeps_3290_ = lean_ctor_get(v___x_3283_, 6);
v_messages_3291_ = lean_ctor_get(v___x_3283_, 7);
v_infoState_3292_ = lean_ctor_get(v___x_3283_, 8);
v_snapshotTasks_3293_ = lean_ctor_get(v___x_3283_, 9);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3295_ = v___x_3283_;
v_isShared_3296_ = v_isSharedCheck_3312_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_snapshotTasks_3293_);
lean_inc(v_infoState_3292_);
lean_inc(v_messages_3291_);
lean_inc(v_recordedDeps_3290_);
lean_inc(v_cache_3289_);
lean_inc(v_traceState_3284_);
lean_inc(v_auxDeclNGen_3288_);
lean_inc(v_ngen_3287_);
lean_inc(v_nextMacroScope_3286_);
lean_inc(v_env_3285_);
lean_dec(v___x_3283_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3312_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
uint64_t v_tid_3297_; lean_object* v_traces_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3311_; 
v_tid_3297_ = lean_ctor_get_uint64(v_traceState_3284_, sizeof(void*)*1);
v_traces_3298_ = lean_ctor_get(v_traceState_3284_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_traceState_3284_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3300_ = v_traceState_3284_;
v_isShared_3301_ = v_isSharedCheck_3311_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_traces_3298_);
lean_dec(v_traceState_3284_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3311_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3302_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3235_, v_traces_3298_);
lean_dec_ref(v_traces_3298_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set(v___x_3300_, 0, v___x_3302_);
v___x_3304_ = v___x_3300_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3302_);
lean_ctor_set_uint64(v_reuseFailAlloc_3310_, sizeof(void*)*1, v_tid_3297_);
v___x_3304_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v___x_3306_; 
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 4, v___x_3304_);
v___x_3306_ = v___x_3295_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_env_3285_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_nextMacroScope_3286_);
lean_ctor_set(v_reuseFailAlloc_3309_, 2, v_ngen_3287_);
lean_ctor_set(v_reuseFailAlloc_3309_, 3, v_auxDeclNGen_3288_);
lean_ctor_set(v_reuseFailAlloc_3309_, 4, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3309_, 5, v_cache_3289_);
lean_ctor_set(v_reuseFailAlloc_3309_, 6, v_recordedDeps_3290_);
lean_ctor_set(v_reuseFailAlloc_3309_, 7, v_messages_3291_);
lean_ctor_set(v_reuseFailAlloc_3309_, 8, v_infoState_3292_);
lean_ctor_set(v_reuseFailAlloc_3309_, 9, v_snapshotTasks_3293_);
v___x_3306_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = lean_st_ref_put(v___y_3243_, v___x_3306_);
v___x_3308_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3245_);
return v___x_3308_;
}
}
}
}
}
else
{
goto v___jp_3276_;
}
}
else
{
goto v___jp_3276_;
}
}
v___jp_3313_:
{
double v___x_3315_; double v___x_3316_; double v___x_3317_; uint8_t v___x_3318_; 
v___x_3315_ = lean_unbox_float(v_snd_3262_);
v___x_3316_ = lean_unbox_float(v_fst_3261_);
v___x_3317_ = lean_float_sub(v___x_3315_, v___x_3316_);
v___x_3318_ = lean_float_decLt(v___y_3314_, v___x_3317_);
v___y_3282_ = v___x_3318_;
goto v___jp_3281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3329_, lean_object* v_collapsed_3330_, lean_object* v_tag_3331_, lean_object* v_opts_3332_, lean_object* v_clsEnabled_3333_, lean_object* v_oldTraces_3334_, lean_object* v_msg_3335_, lean_object* v_resStartStop_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
uint8_t v_collapsed_boxed_3344_; uint8_t v_clsEnabled_boxed_3345_; lean_object* v_res_3346_; 
v_collapsed_boxed_3344_ = lean_unbox(v_collapsed_3330_);
v_clsEnabled_boxed_3345_ = lean_unbox(v_clsEnabled_3333_);
v_res_3346_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3329_, v_collapsed_boxed_3344_, v_tag_3331_, v_opts_3332_, v_clsEnabled_boxed_3345_, v_oldTraces_3334_, v_msg_3335_, v_resStartStop_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v_opts_3332_);
return v_res_3346_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = lean_unsigned_to_nat(32u);
v___x_3348_ = lean_mk_empty_array_with_capacity(v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3350_ = ((size_t)5ULL);
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = lean_unsigned_to_nat(32u);
v___x_3353_ = lean_mk_empty_array_with_capacity(v___x_3352_);
v___x_3354_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3355_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v___x_3353_);
lean_ctor_set(v___x_3355_, 2, v___x_3351_);
lean_ctor_set(v___x_3355_, 3, v___x_3351_);
lean_ctor_set_usize(v___x_3355_, 4, v___x_3350_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; lean_object* v_traceState_3359_; lean_object* v_traces_3360_; lean_object* v___x_3361_; lean_object* v_traceState_3362_; lean_object* v_env_3363_; lean_object* v_nextMacroScope_3364_; lean_object* v_ngen_3365_; lean_object* v_auxDeclNGen_3366_; lean_object* v_cache_3367_; lean_object* v_recordedDeps_3368_; lean_object* v_messages_3369_; lean_object* v_infoState_3370_; lean_object* v_snapshotTasks_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3390_; 
v___x_3358_ = lean_st_ref_get(v___y_3356_);
v_traceState_3359_ = lean_ctor_get(v___x_3358_, 4);
lean_inc_ref(v_traceState_3359_);
lean_dec(v___x_3358_);
v_traces_3360_ = lean_ctor_get(v_traceState_3359_, 0);
lean_inc_ref(v_traces_3360_);
lean_dec_ref(v_traceState_3359_);
v___x_3361_ = lean_st_ref_take(v___y_3356_);
v_traceState_3362_ = lean_ctor_get(v___x_3361_, 4);
v_env_3363_ = lean_ctor_get(v___x_3361_, 0);
v_nextMacroScope_3364_ = lean_ctor_get(v___x_3361_, 1);
v_ngen_3365_ = lean_ctor_get(v___x_3361_, 2);
v_auxDeclNGen_3366_ = lean_ctor_get(v___x_3361_, 3);
v_cache_3367_ = lean_ctor_get(v___x_3361_, 5);
v_recordedDeps_3368_ = lean_ctor_get(v___x_3361_, 6);
v_messages_3369_ = lean_ctor_get(v___x_3361_, 7);
v_infoState_3370_ = lean_ctor_get(v___x_3361_, 8);
v_snapshotTasks_3371_ = lean_ctor_get(v___x_3361_, 9);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3373_ = v___x_3361_;
v_isShared_3374_ = v_isSharedCheck_3390_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_snapshotTasks_3371_);
lean_inc(v_infoState_3370_);
lean_inc(v_messages_3369_);
lean_inc(v_recordedDeps_3368_);
lean_inc(v_cache_3367_);
lean_inc(v_traceState_3362_);
lean_inc(v_auxDeclNGen_3366_);
lean_inc(v_ngen_3365_);
lean_inc(v_nextMacroScope_3364_);
lean_inc(v_env_3363_);
lean_dec(v___x_3361_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3390_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
uint64_t v_tid_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3388_; 
v_tid_3375_ = lean_ctor_get_uint64(v_traceState_3362_, sizeof(void*)*1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_traceState_3362_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v_traceState_3362_, 0);
lean_dec(v_unused_3389_);
v___x_3377_ = v_traceState_3362_;
v_isShared_3378_ = v_isSharedCheck_3388_;
goto v_resetjp_3376_;
}
else
{
lean_dec(v_traceState_3362_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3388_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3379_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3379_);
v___x_3381_ = v___x_3377_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3379_);
lean_ctor_set_uint64(v_reuseFailAlloc_3387_, sizeof(void*)*1, v_tid_3375_);
v___x_3381_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 4, v___x_3381_);
v___x_3383_ = v___x_3373_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_env_3363_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_nextMacroScope_3364_);
lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_ngen_3365_);
lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_auxDeclNGen_3366_);
lean_ctor_set(v_reuseFailAlloc_3386_, 4, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3386_, 5, v_cache_3367_);
lean_ctor_set(v_reuseFailAlloc_3386_, 6, v_recordedDeps_3368_);
lean_ctor_set(v_reuseFailAlloc_3386_, 7, v_messages_3369_);
lean_ctor_set(v_reuseFailAlloc_3386_, 8, v_infoState_3370_);
lean_ctor_set(v_reuseFailAlloc_3386_, 9, v_snapshotTasks_3371_);
v___x_3383_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_st_ref_put(v___y_3356_, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v_traces_3360_);
return v___x_3385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3391_);
lean_dec(v___y_3391_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
lean_inc(v___y_3396_);
lean_inc(v___y_3395_);
v___x_3402_ = lean_apply_7(v_x_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, lean_box(0));
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3412_, lean_object* v_localInsts_3413_, lean_object* v_x_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___f_3422_; lean_object* v___x_3423_; 
lean_inc(v___y_3416_);
lean_inc(v___y_3415_);
v___f_3422_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3422_, 0, v_x_3414_);
lean_closure_set(v___f_3422_, 1, v___y_3415_);
lean_closure_set(v___f_3422_, 2, v___y_3416_);
v___x_3423_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3412_, v_localInsts_3413_, v___f_3422_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3423_) == 0)
{
return v___x_3423_;
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3432_, lean_object* v_localInsts_3433_, lean_object* v_x_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3432_, v_localInsts_3433_, v_x_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; lean_object* v_ngen_3446_; lean_object* v_namePrefix_3447_; lean_object* v_idx_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3478_; 
v___x_3445_ = lean_st_ref_get(v___y_3443_);
v_ngen_3446_ = lean_ctor_get(v___x_3445_, 2);
lean_inc_ref(v_ngen_3446_);
lean_dec(v___x_3445_);
v_namePrefix_3447_ = lean_ctor_get(v_ngen_3446_, 0);
v_idx_3448_ = lean_ctor_get(v_ngen_3446_, 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_ngen_3446_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3450_ = v_ngen_3446_;
v_isShared_3451_ = v_isSharedCheck_3478_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_idx_3448_);
lean_inc(v_namePrefix_3447_);
lean_dec(v_ngen_3446_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3478_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_r_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
lean_inc(v_idx_3448_);
lean_inc(v_namePrefix_3447_);
v_r_3452_ = l_Lean_Name_num___override(v_namePrefix_3447_, v_idx_3448_);
v___x_3453_ = lean_unsigned_to_nat(1u);
v___x_3454_ = lean_nat_add(v_idx_3448_, v___x_3453_);
lean_dec(v_idx_3448_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v___x_3454_);
v___x_3456_ = v___x_3450_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_namePrefix_3447_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; lean_object* v_env_3458_; lean_object* v_nextMacroScope_3459_; lean_object* v_auxDeclNGen_3460_; lean_object* v_traceState_3461_; lean_object* v_cache_3462_; lean_object* v_recordedDeps_3463_; lean_object* v_messages_3464_; lean_object* v_infoState_3465_; lean_object* v_snapshotTasks_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3475_; 
v___x_3457_ = lean_st_ref_take(v___y_3443_);
v_env_3458_ = lean_ctor_get(v___x_3457_, 0);
v_nextMacroScope_3459_ = lean_ctor_get(v___x_3457_, 1);
v_auxDeclNGen_3460_ = lean_ctor_get(v___x_3457_, 3);
v_traceState_3461_ = lean_ctor_get(v___x_3457_, 4);
v_cache_3462_ = lean_ctor_get(v___x_3457_, 5);
v_recordedDeps_3463_ = lean_ctor_get(v___x_3457_, 6);
v_messages_3464_ = lean_ctor_get(v___x_3457_, 7);
v_infoState_3465_ = lean_ctor_get(v___x_3457_, 8);
v_snapshotTasks_3466_ = lean_ctor_get(v___x_3457_, 9);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3457_, 2);
lean_dec(v_unused_3476_);
v___x_3468_ = v___x_3457_;
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_snapshotTasks_3466_);
lean_inc(v_infoState_3465_);
lean_inc(v_messages_3464_);
lean_inc(v_recordedDeps_3463_);
lean_inc(v_cache_3462_);
lean_inc(v_traceState_3461_);
lean_inc(v_auxDeclNGen_3460_);
lean_inc(v_nextMacroScope_3459_);
lean_inc(v_env_3458_);
lean_dec(v___x_3457_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 2, v___x_3456_);
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_env_3458_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_nextMacroScope_3459_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v_auxDeclNGen_3460_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_traceState_3461_);
lean_ctor_set(v_reuseFailAlloc_3474_, 5, v_cache_3462_);
lean_ctor_set(v_reuseFailAlloc_3474_, 6, v_recordedDeps_3463_);
lean_ctor_set(v_reuseFailAlloc_3474_, 7, v_messages_3464_);
lean_ctor_set(v_reuseFailAlloc_3474_, 8, v_infoState_3465_);
lean_ctor_set(v_reuseFailAlloc_3474_, 9, v_snapshotTasks_3466_);
v___x_3471_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_st_ref_put(v___y_3443_, v___x_3471_);
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_r_3452_);
return v___x_3473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3479_);
lean_dec(v___y_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_3489_; lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v___x_3489_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3487_);
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec(v___y_3498_);
return v_res_3505_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3514_, lean_object* v_x_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___x_3523_; lean_object* v___y_3525_; uint8_t v___x_3534_; 
v___x_3523_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3534_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3516_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; 
v___x_3535_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3525_ = v___x_3535_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3536_; 
v___x_3536_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3525_ = v___x_3536_;
goto v___jp_3524_;
}
v___jp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
lean_inc_ref(v___y_3525_);
v___x_3526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___y_3525_);
v___x_3527_ = l_Lean_MessageData_ofFormat(v___x_3526_);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3523_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_indentExpr(v_e_3514_);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
return v___x_3533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3537_, lean_object* v_x_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3537_, v_x_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v_x_3538_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3547_, lean_object* v_x_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_keyedConfig_3556_; uint8_t v_trackZetaDelta_3557_; lean_object* v_zetaDeltaSet_3558_; lean_object* v_localInstances_3559_; lean_object* v_defEqCtx_x3f_3560_; lean_object* v_synthPendingDepth_3561_; lean_object* v_customCanUnfoldPredicate_x3f_3562_; uint8_t v_univApprox_3563_; uint8_t v_inTypeClassResolution_3564_; uint8_t v_cacheInferType_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_keyedConfig_3556_ = lean_ctor_get(v___y_3551_, 0);
v_trackZetaDelta_3557_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*7);
v_zetaDeltaSet_3558_ = lean_ctor_get(v___y_3551_, 1);
v_localInstances_3559_ = lean_ctor_get(v___y_3551_, 3);
v_defEqCtx_x3f_3560_ = lean_ctor_get(v___y_3551_, 4);
v_synthPendingDepth_3561_ = lean_ctor_get(v___y_3551_, 5);
v_customCanUnfoldPredicate_x3f_3562_ = lean_ctor_get(v___y_3551_, 6);
v_univApprox_3563_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3564_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*7 + 2);
v_cacheInferType_3565_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3562_);
lean_inc(v_synthPendingDepth_3561_);
lean_inc(v_defEqCtx_x3f_3560_);
lean_inc_ref(v_localInstances_3559_);
lean_inc(v_zetaDeltaSet_3558_);
lean_inc_ref(v_keyedConfig_3556_);
v___x_3566_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3566_, 0, v_keyedConfig_3556_);
lean_ctor_set(v___x_3566_, 1, v_zetaDeltaSet_3558_);
lean_ctor_set(v___x_3566_, 2, v_lctx_3547_);
lean_ctor_set(v___x_3566_, 3, v_localInstances_3559_);
lean_ctor_set(v___x_3566_, 4, v_defEqCtx_x3f_3560_);
lean_ctor_set(v___x_3566_, 5, v_synthPendingDepth_3561_);
lean_ctor_set(v___x_3566_, 6, v_customCanUnfoldPredicate_x3f_3562_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7, v_trackZetaDelta_3557_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7 + 1, v_univApprox_3563_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3564_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7 + 3, v_cacheInferType_3565_);
lean_inc(v___y_3554_);
lean_inc_ref(v___y_3553_);
lean_inc(v___y_3552_);
lean_inc(v___y_3550_);
lean_inc(v___y_3549_);
v___x_3567_ = lean_apply_7(v_x_3548_, v___y_3549_, v___y_3550_, v___x_3566_, v___y_3552_, v___y_3553_, v___y_3554_, lean_box(0));
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
else
{
return v___x_3567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3576_, lean_object* v_x_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3576_, v_x_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec(v___y_3578_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3588_, lean_object* v_letFVars_3589_, lean_object* v_lctx_3590_, lean_object* v_v_3591_, lean_object* v_e_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3600_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3601_ = lean_expr_instantiate_rev(v_e_3592_, v_fvars_3588_);
v___x_3602_ = lean_apply_1(v_v_3591_, v___x_3601_);
v___x_3603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3603_, 0, lean_box(0));
lean_closure_set(v___x_3603_, 1, v_letFVars_3589_);
lean_closure_set(v___x_3603_, 2, v___x_3602_);
v___x_3604_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3590_, v___x_3600_, v___x_3603_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3605_, lean_object* v_letFVars_3606_, lean_object* v_lctx_3607_, lean_object* v_v_3608_, lean_object* v_e_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3605_, v_letFVars_3606_, v_lctx_3607_, v_v_3608_, v_e_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v_e_3609_);
lean_dec_ref(v_fvars_3605_);
return v_res_3617_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3620_ = l_Lean_stringToMessageData(v___x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
lean_inc_ref(v_a_3621_);
v___x_3630_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3621_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v_expr_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3682_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_expr_3632_ = lean_ctor_get(v_a_3622_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_a_3622_);
if (v_isSharedCheck_3682_ == 0)
{
lean_object* v_unused_3683_; 
v_unused_3683_ = lean_ctor_get(v_a_3622_, 1);
lean_dec(v_unused_3683_);
v___x_3634_ = v_a_3622_;
v_isShared_3635_ = v_isSharedCheck_3682_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_expr_3632_);
lean_dec(v_a_3622_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3682_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; 
lean_inc(v_a_3631_);
lean_inc_ref(v_expr_3632_);
v___x_3636_ = l_Lean_Meta_isExprDefEq(v_expr_3632_, v_a_3631_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3673_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3673_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3673_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_unbox(v_a_3637_);
lean_dec(v_a_3637_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_del_object(v___x_3639_);
v___x_3642_ = lean_box(0);
v___x_3643_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3644_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3631_, v_expr_3632_, v___x_3642_, v___x_3643_, v___y_3625_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v_expr_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3659_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v_expr_3646_ = lean_ctor_get(v_a_3621_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3621_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v_a_3621_, 1);
lean_dec(v_unused_3660_);
v___x_3648_ = v_a_3621_;
v_isShared_3649_ = v_isSharedCheck_3659_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_expr_3646_);
lean_dec(v_a_3621_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3659_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3653_; 
v___x_3650_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3651_ = l_Lean_indentExpr(v_expr_3646_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set_tag(v___x_3648_, 7);
lean_ctor_set(v___x_3648_, 1, v___x_3651_);
lean_ctor_set(v___x_3648_, 0, v___x_3650_);
v___x_3653_ = v___x_3648_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3655_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set_tag(v___x_3634_, 7);
lean_ctor_set(v___x_3634_, 1, v_a_3645_);
lean_ctor_set(v___x_3634_, 0, v___x_3653_);
v___x_3655_ = v___x_3634_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_a_3645_);
v___x_3655_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3655_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_del_object(v___x_3634_);
lean_dec_ref(v_a_3621_);
v_a_3661_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3644_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3644_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
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
lean_object* v___x_3669_; lean_object* v___x_3671_; 
lean_del_object(v___x_3634_);
lean_dec_ref(v_expr_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3621_);
v___x_3669_ = lean_box(0);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3669_);
v___x_3671_ = v___x_3639_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_del_object(v___x_3634_);
lean_dec_ref(v_expr_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3621_);
v_a_3674_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3636_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3636_);
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
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec_ref(v_a_3622_);
lean_dec_ref(v_a_3621_);
v_a_3684_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3630_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3630_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3692_, v_a_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec(v___y_3694_);
return v_res_3701_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3704_ = l_Lean_stringToMessageData(v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
if (lean_obj_tag(v_e_3705_) == 5)
{
lean_object* v_fn_3713_; lean_object* v_arg_3714_; lean_object* v___x_3715_; 
v_fn_3713_ = lean_ctor_get(v_e_3705_, 0);
v_arg_3714_ = lean_ctor_get(v_e_3705_, 1);
lean_inc_ref(v_fn_3713_);
v___x_3715_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3713_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
lean_inc_ref(v_arg_3714_);
v___x_3717_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3714_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3740_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3740_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3740_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_expr_3722_; size_t v___x_3723_; size_t v___x_3724_; uint8_t v___x_3725_; 
v_expr_3722_ = lean_ctor_get(v_a_3718_, 0);
lean_inc_ref(v_expr_3722_);
lean_dec(v_a_3718_);
v___x_3723_ = lean_ptr_addr(v_fn_3713_);
v___x_3724_ = lean_ptr_addr(v_a_3716_);
v___x_3725_ = lean_usize_dec_eq(v___x_3723_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_dec_ref_known(v_e_3705_, 2);
v___x_3726_ = l_Lean_Expr_app___override(v_a_3716_, v_expr_3722_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3726_);
v___x_3728_ = v___x_3720_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
else
{
size_t v___x_3730_; size_t v___x_3731_; uint8_t v___x_3732_; 
v___x_3730_ = lean_ptr_addr(v_arg_3714_);
v___x_3731_ = lean_ptr_addr(v_expr_3722_);
v___x_3732_ = lean_usize_dec_eq(v___x_3730_, v___x_3731_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_dec_ref_known(v_e_3705_, 2);
v___x_3733_ = l_Lean_Expr_app___override(v_a_3716_, v_expr_3722_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3733_);
v___x_3735_ = v___x_3720_;
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
lean_object* v___x_3738_; 
lean_dec_ref(v_expr_3722_);
lean_dec(v_a_3716_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_e_3705_);
v___x_3738_ = v___x_3720_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_e_3705_);
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
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v_a_3716_);
lean_dec_ref_known(v_e_3705_, 2);
v_a_3741_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3717_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3717_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3705_, 2);
return v___x_3715_;
}
}
else
{
lean_object* v___x_3749_; 
v___x_3749_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3758_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_expr_3754_; lean_object* v___x_3756_; 
v_expr_3754_ = lean_ctor_get(v_a_3750_, 0);
lean_inc_ref(v_expr_3754_);
lean_dec(v_a_3750_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v_expr_3754_);
v___x_3756_ = v___x_3752_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_expr_3754_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
v_a_3759_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3749_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3749_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec(v_a_3768_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
if (lean_obj_tag(v_e_3776_) == 5)
{
lean_object* v_fn_3784_; lean_object* v_arg_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_fn_3784_ = lean_ctor_get(v_e_3776_, 0);
v_arg_3785_ = lean_ctor_get(v_e_3776_, 1);
lean_inc_ref_n(v_fn_3784_, 2);
v___x_3786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3786_, 0, v_fn_3784_);
v___x_3787_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3784_, v___x_3786_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v___x_3787_, 1);
lean_inc_ref(v_arg_3785_);
v___x_3789_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3785_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v___x_3791_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3776_, v_a_3788_, v_a_3790_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
return v___x_3791_;
}
else
{
lean_dec(v_a_3788_);
lean_dec_ref_known(v_e_3776_, 2);
return v___x_3789_;
}
}
else
{
lean_dec_ref_known(v_e_3776_, 2);
return v___x_3787_;
}
}
else
{
lean_object* v___x_3792_; 
v___x_3792_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_){
_start:
{
uint8_t v___x_3801_; 
v___x_3801_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3794_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3812_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3812_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3812_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3807_ = lean_box(0);
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v_a_3803_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3808_);
v___x_3810_ = v___x_3805_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_a_3813_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3802_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3802_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_Expr_getAppFn(v_e_3793_);
if (lean_obj_tag(v___x_3821_) == 2)
{
lean_object* v_mvarId_3822_; lean_object* v_dummy_3823_; lean_object* v_nargs_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_mvarId_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_mvarId_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v_dummy_3823_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3824_ = l_Lean_Expr_getAppNumArgs(v_e_3793_);
lean_inc(v_nargs_3824_);
v___x_3825_ = lean_mk_array(v_nargs_3824_, v_dummy_3823_);
v___x_3826_ = lean_unsigned_to_nat(1u);
v___x_3827_ = lean_nat_sub(v_nargs_3824_, v___x_3826_);
lean_dec(v_nargs_3824_);
lean_inc_ref(v_e_3793_);
v___x_3828_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3793_, v___x_3825_, v___x_3827_);
v___x_3829_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3822_, v___x_3828_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_mvarId_3822_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v___x_3830_; 
lean_dec_ref_known(v___x_3829_, 1);
v___x_3830_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
return v___x_3830_;
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v_e_3793_);
v_a_3831_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3829_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3829_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v___x_3839_; 
lean_dec_ref(v___x_3821_);
v___x_3839_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
return v___x_3839_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec(v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec(v_a_3841_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
v___x_3859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3858_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
return v___x_3859_;
}
else
{
return v___x_3857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec(v_a_3861_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3869_, lean_object* v_fvars_3870_, lean_object* v_doms_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3869_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3870_, v_doms_3871_, v_a_3880_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
return v___x_3881_;
}
else
{
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3882_, lean_object* v_fvars_3883_, lean_object* v_doms_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3882_, v_fvars_3883_, v_doms_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v_doms_3884_);
lean_dec_ref(v_fvars_3883_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3893_, lean_object* v_fvars_3894_, lean_object* v_doms_3895_, lean_object* v_e_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3896_, v_a_3898_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
if (lean_obj_tag(v_a_3905_) == 1)
{
lean_object* v_val_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v_e_3896_);
v_val_3906_ = lean_ctor_get(v_a_3905_, 0);
lean_inc(v_val_3906_);
lean_dec_ref_known(v_a_3905_, 1);
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3908_, 0, v_fvars_3894_);
lean_closure_set(v___x_3908_, 1, v_doms_3895_);
lean_closure_set(v___x_3908_, 2, v_val_3906_);
v___x_3909_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3893_, v___x_3907_, v___x_3908_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
return v___x_3909_;
}
else
{
lean_dec(v_a_3905_);
if (lean_obj_tag(v_e_3896_) == 7)
{
lean_object* v_binderName_3910_; lean_object* v_binderType_3911_; lean_object* v_body_3912_; uint8_t v_binderInfo_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v_binderName_3910_ = lean_ctor_get(v_e_3896_, 0);
lean_inc(v_binderName_3910_);
v_binderType_3911_ = lean_ctor_get(v_e_3896_, 1);
lean_inc_ref(v_binderType_3911_);
v_body_3912_ = lean_ctor_get(v_e_3896_, 2);
lean_inc_ref(v_body_3912_);
v_binderInfo_3913_ = lean_ctor_get_uint8(v_e_3896_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3896_, 3);
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3915_ = lean_expr_instantiate_rev(v_binderType_3911_, v_fvars_3894_);
lean_dec_ref(v_binderType_3911_);
v___x_3916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3916_, 0, v___x_3915_);
lean_inc_ref(v_lctx_3893_);
v___x_3917_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3893_, v___x_3914_, v___x_3916_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v_expr_3921_; uint8_t v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc_n(v_a_3920_, 2);
lean_dec_ref_known(v___x_3919_, 1);
v_expr_3921_ = lean_ctor_get(v_a_3918_, 0);
v___x_3922_ = 0;
lean_inc_ref(v_expr_3921_);
v___x_3923_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3893_, v_a_3920_, v_binderName_3910_, v_expr_3921_, v_binderInfo_3913_, v___x_3922_);
v___x_3924_ = l_Lean_Expr_fvar___override(v_a_3920_);
v___x_3925_ = lean_array_push(v_fvars_3894_, v___x_3924_);
v___x_3926_ = lean_array_push(v_doms_3895_, v_a_3918_);
v_lctx_3893_ = v___x_3923_;
v_fvars_3894_ = v___x_3925_;
v_doms_3895_ = v___x_3926_;
v_e_3896_ = v_body_3912_;
goto _start;
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v_a_3918_);
lean_dec_ref(v_body_3912_);
lean_dec(v_binderName_3910_);
lean_dec_ref(v_doms_3895_);
lean_dec_ref(v_fvars_3894_);
lean_dec_ref(v_lctx_3893_);
v_a_3928_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3919_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3919_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_dec_ref(v_body_3912_);
lean_dec(v_binderName_3910_);
lean_dec_ref(v_doms_3895_);
lean_dec_ref(v_fvars_3894_);
lean_dec_ref(v_lctx_3893_);
return v___x_3917_;
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___f_3938_; lean_object* v___x_3939_; 
v___x_3936_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3937_ = lean_expr_instantiate_rev(v_e_3896_, v_fvars_3894_);
lean_dec_ref(v_e_3896_);
v___f_3938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3938_, 0, v___x_3937_);
lean_closure_set(v___f_3938_, 1, v_fvars_3894_);
lean_closure_set(v___f_3938_, 2, v_doms_3895_);
v___x_3939_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3893_, v___x_3936_, v___f_3938_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
return v___x_3939_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec_ref(v_e_3896_);
lean_dec_ref(v_doms_3895_);
lean_dec_ref(v_fvars_3894_);
lean_dec_ref(v_lctx_3893_);
v_a_3940_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3904_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3904_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_){
_start:
{
uint32_t v___x_3956_; uint8_t v___x_3957_; 
v___x_3956_ = 5;
v___x_3957_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3948_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_object* v_lctx_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_lctx_3958_ = lean_ctor_get(v_a_3951_, 2);
v___x_3959_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3958_);
v___x_3960_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3958_, v___x_3959_, v___x_3959_, v_e_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v_e_3948_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec(v_a_3965_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_3973_, lean_object* v_e_3974_, lean_object* v_typeName_3975_, lean_object* v_idx_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_3973_, v_e_3974_, v_typeName_3975_, v_idx_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec(v___y_3977_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec(v_a_3986_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4005_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v___x_4005_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_3994_, v_a_4004_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
return v___x_4005_;
}
else
{
lean_dec_ref(v_fvars_3994_);
return v___x_4003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec(v___y_4008_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4016_, lean_object* v_fvars_4017_, lean_object* v_e_4018_, lean_object* v_letFVars_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
switch(lean_obj_tag(v_e_4018_))
{
case 6:
{
lean_object* v_binderName_4027_; lean_object* v_binderType_4028_; lean_object* v_body_4029_; uint8_t v_binderInfo_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_binderName_4027_ = lean_ctor_get(v_e_4018_, 0);
lean_inc(v_binderName_4027_);
v_binderType_4028_ = lean_ctor_get(v_e_4018_, 1);
lean_inc_ref(v_binderType_4028_);
v_body_4029_ = lean_ctor_get(v_e_4018_, 2);
lean_inc_ref(v_body_4029_);
v_binderInfo_4030_ = lean_ctor_get_uint8(v_e_4018_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4018_, 3);
v___x_4031_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4016_);
lean_inc(v_letFVars_4019_);
v___x_4032_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4017_, v_letFVars_4019_, v_lctx_4016_, v___x_4031_, v_binderType_4028_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec_ref(v_binderType_4028_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v___x_4034_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v_expr_4036_; uint8_t v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc_n(v_a_4035_, 2);
lean_dec_ref_known(v___x_4034_, 1);
v_expr_4036_ = lean_ctor_get(v_a_4033_, 0);
lean_inc_ref(v_expr_4036_);
lean_dec(v_a_4033_);
v___x_4037_ = 0;
v___x_4038_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4016_, v_a_4035_, v_binderName_4027_, v_expr_4036_, v_binderInfo_4030_, v___x_4037_);
v___x_4039_ = l_Lean_Expr_fvar___override(v_a_4035_);
v___x_4040_ = lean_array_push(v_fvars_4017_, v___x_4039_);
v_lctx_4016_ = v___x_4038_;
v_fvars_4017_ = v___x_4040_;
v_e_4018_ = v_body_4029_;
goto _start;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec(v_a_4033_);
lean_dec_ref(v_body_4029_);
lean_dec(v_binderName_4027_);
lean_dec(v_letFVars_4019_);
lean_dec_ref(v_fvars_4017_);
lean_dec_ref(v_lctx_4016_);
v_a_4042_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4034_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4034_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
else
{
lean_dec_ref(v_body_4029_);
lean_dec(v_binderName_4027_);
lean_dec(v_letFVars_4019_);
lean_dec_ref(v_fvars_4017_);
lean_dec_ref(v_lctx_4016_);
return v___x_4032_;
}
}
case 8:
{
lean_object* v_declName_4050_; lean_object* v_type_4051_; lean_object* v_value_4052_; lean_object* v_body_4053_; uint8_t v_nondep_4054_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_declName_4050_ = lean_ctor_get(v_e_4018_, 0);
lean_inc(v_declName_4050_);
v_type_4051_ = lean_ctor_get(v_e_4018_, 1);
lean_inc_ref(v_type_4051_);
v_value_4052_ = lean_ctor_get(v_e_4018_, 2);
lean_inc_ref(v_value_4052_);
v_body_4053_ = lean_ctor_get(v_e_4018_, 3);
lean_inc_ref(v_body_4053_);
v_nondep_4054_ = lean_ctor_get_uint8(v_e_4018_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4018_, 4);
v___x_4068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4016_);
lean_inc(v_letFVars_4019_);
v___x_4069_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4017_, v_letFVars_4019_, v_lctx_4016_, v___x_4068_, v_type_4051_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec_ref(v_type_4051_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v___x_4071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4016_);
lean_inc(v_letFVars_4019_);
v___x_4072_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4017_, v_letFVars_4019_, v_lctx_4016_, v___x_4071_, v_value_4052_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec_ref(v_value_4052_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; uint8_t v___x_4103_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4072_, 1);
v___x_4103_ = l_List_isEmpty___redArg(v_letFVars_4019_);
if (v___x_4103_ == 0)
{
lean_object* v___f_4104_; lean_object* v___x_4105_; 
lean_inc(v_a_4070_);
lean_inc(v_a_4073_);
v___f_4104_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4104_, 0, v_a_4073_);
lean_closure_set(v___f_4104_, 1, v_a_4070_);
lean_inc_ref(v_lctx_4016_);
v___x_4105_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4016_, v___f_4104_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_dec_ref_known(v___x_4105_, 1);
v___y_4075_ = v_a_4020_;
v___y_4076_ = v_a_4021_;
v___y_4077_ = v_a_4022_;
v___y_4078_ = v_a_4023_;
v___y_4079_ = v_a_4024_;
v___y_4080_ = v_a_4025_;
goto v___jp_4074_;
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v_a_4073_);
lean_dec(v_a_4070_);
lean_dec_ref(v_body_4053_);
lean_dec(v_declName_4050_);
lean_dec(v_letFVars_4019_);
lean_dec_ref(v_fvars_4017_);
lean_dec_ref(v_lctx_4016_);
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4105_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
else
{
v___y_4075_ = v_a_4020_;
v___y_4076_ = v_a_4021_;
v___y_4077_ = v_a_4022_;
v___y_4078_ = v_a_4023_;
v___y_4079_ = v_a_4024_;
v___y_4080_ = v_a_4025_;
goto v___jp_4074_;
}
v___jp_4074_:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v_expr_4083_; lean_object* v_expr_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4093_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
v_expr_4083_ = lean_ctor_get(v_a_4070_, 0);
lean_inc_ref(v_expr_4083_);
lean_dec(v_a_4070_);
v_expr_4084_ = lean_ctor_get(v_a_4073_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_a_4073_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v_a_4073_, 1);
lean_dec(v_unused_4094_);
v___x_4086_ = v_a_4073_;
v_isShared_4087_ = v_isSharedCheck_4093_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_expr_4084_);
lean_dec(v_a_4073_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4093_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
uint8_t v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = 0;
lean_inc(v_a_4082_);
v___x_4089_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4016_, v_a_4082_, v_declName_4050_, v_expr_4083_, v_expr_4084_, v_nondep_4054_, v___x_4088_);
if (v_nondep_4054_ == 0)
{
lean_object* v___x_4091_; 
lean_inc(v_a_4082_);
if (v_isShared_4087_ == 0)
{
lean_ctor_set_tag(v___x_4086_, 1);
lean_ctor_set(v___x_4086_, 1, v_letFVars_4019_);
lean_ctor_set(v___x_4086_, 0, v_a_4082_);
v___x_4091_ = v___x_4086_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4082_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_letFVars_4019_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
v___y_4056_ = v_a_4082_;
v___y_4057_ = v___y_4077_;
v___y_4058_ = v___y_4078_;
v___y_4059_ = v___y_4080_;
v___y_4060_ = v___x_4089_;
v___y_4061_ = v___y_4075_;
v___y_4062_ = v___y_4079_;
v___y_4063_ = v___y_4076_;
v___y_4064_ = v___x_4091_;
goto v___jp_4055_;
}
}
else
{
lean_del_object(v___x_4086_);
v___y_4056_ = v_a_4082_;
v___y_4057_ = v___y_4077_;
v___y_4058_ = v___y_4078_;
v___y_4059_ = v___y_4080_;
v___y_4060_ = v___x_4089_;
v___y_4061_ = v___y_4075_;
v___y_4062_ = v___y_4079_;
v___y_4063_ = v___y_4076_;
v___y_4064_ = v_letFVars_4019_;
goto v___jp_4055_;
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec(v_a_4073_);
lean_dec(v_a_4070_);
lean_dec_ref(v_body_4053_);
lean_dec(v_declName_4050_);
lean_dec(v_letFVars_4019_);
lean_dec_ref(v_fvars_4017_);
lean_dec_ref(v_lctx_4016_);
v_a_4095_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4081_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4081_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
else
{
lean_dec(v_a_4070_);
lean_dec_ref(v_body_4053_);
lean_dec(v_declName_4050_);
lean_dec(v_letFVars_4019_);
lean_dec_ref(v_fvars_4017_);
lean_dec_ref(v_lctx_4016_);
return v___x_4072_;
}
}
else
{
lean_dec_ref(v_body_4053_);
lean_dec_ref(v_value_4052_);
lean_dec(v_declName_4050_);
lean_dec(v_letFVars_4019_);
lean_dec_ref(v_fvars_4017_);
lean_dec_ref(v_lctx_4016_);
return v___x_4069_;
}
v___jp_4055_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = l_Lean_Expr_fvar___override(v___y_4056_);
v___x_4066_ = lean_array_push(v_fvars_4017_, v___x_4065_);
v_lctx_4016_ = v___y_4060_;
v_fvars_4017_ = v___x_4066_;
v_e_4018_ = v_body_4053_;
v_letFVars_4019_ = v___y_4064_;
v_a_4020_ = v___y_4061_;
v_a_4021_ = v___y_4063_;
v_a_4022_ = v___y_4057_;
v_a_4023_ = v___y_4058_;
v_a_4024_ = v___y_4062_;
v_a_4025_ = v___y_4059_;
goto _start;
}
}
default: 
{
lean_object* v___f_4114_; lean_object* v___x_4115_; 
lean_inc_ref(v_fvars_4017_);
v___f_4114_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4114_, 0, v_fvars_4017_);
v___x_4115_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4017_, v_letFVars_4019_, v_lctx_4016_, v___f_4114_, v_e_4018_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec_ref(v_e_4018_);
lean_dec_ref(v_fvars_4017_);
return v___x_4115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_){
_start:
{
uint32_t v___x_4124_; uint8_t v___x_4125_; 
v___x_4124_ = 5;
v___x_4125_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4116_, v___x_4124_);
if (v___x_4125_ == 0)
{
lean_object* v_lctx_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v_lctx_4126_ = lean_ctor_get(v_a_4119_, 2);
v___x_4127_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4117_);
lean_inc_ref(v_lctx_4126_);
v___x_4128_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4126_, v___x_4127_, v_e_4116_, v_a_4117_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
return v___x_4128_;
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4129_ = lean_box(0);
v___x_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4130_, 0, v_e_4116_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
return v___x_4131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec(v_a_4133_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
switch(lean_obj_tag(v_e_4141_))
{
case 0:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4149_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4150_ = l_Lean_MessageData_ofExpr(v_e_4141_);
v___x_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4151_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4152_;
}
case 1:
{
lean_object* v___x_4153_; 
v___x_4153_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4141_, v___y_4144_, v___y_4146_, v___y_4147_);
return v___x_4153_;
}
case 2:
{
lean_object* v___x_4154_; 
v___x_4154_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4154_;
}
case 3:
{
lean_object* v_u_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v_u_4155_ = lean_ctor_get(v_e_4141_, 0);
lean_inc(v_u_4155_);
v___x_4156_ = l_Lean_Level_succ___override(v_u_4155_);
v___x_4157_ = l_Lean_Expr_sort___override(v___x_4156_);
v___x_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v_e_4141_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
return v___x_4160_;
}
case 4:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4161_;
}
case 5:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_inc_ref(v_e_4141_);
v___x_4162_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4162_, 0, v_e_4141_);
v___x_4163_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4141_, v___x_4162_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4163_;
}
case 7:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_inc_ref(v_e_4141_);
v___x_4164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4164_, 0, v_e_4141_);
v___x_4165_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4141_, v___x_4164_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4165_;
}
case 9:
{
lean_object* v_a_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_a_4166_ = lean_ctor_get(v_e_4141_, 0);
v___x_4167_ = l_Lean_Literal_type(v_a_4166_);
v___x_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v_e_4141_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
case 10:
{
lean_object* v_data_4171_; lean_object* v_expr_4172_; lean_object* v___x_4173_; 
v_data_4171_ = lean_ctor_get(v_e_4141_, 0);
v_expr_4172_ = lean_ctor_get(v_e_4141_, 1);
lean_inc_ref(v_expr_4172_);
v___x_4173_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4172_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4196_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4196_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4196_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v_expr_4178_; lean_object* v_type_x3f_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4195_; 
v_expr_4178_ = lean_ctor_get(v_a_4174_, 0);
v_type_x3f_4179_ = lean_ctor_get(v_a_4174_, 1);
v_isSharedCheck_4195_ = !lean_is_exclusive(v_a_4174_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4181_ = v_a_4174_;
v_isShared_4182_ = v_isSharedCheck_4195_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_type_x3f_4179_);
lean_inc(v_expr_4178_);
lean_dec(v_a_4174_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4195_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___y_4184_; size_t v___x_4191_; size_t v___x_4192_; uint8_t v___x_4193_; 
v___x_4191_ = lean_ptr_addr(v_expr_4172_);
v___x_4192_ = lean_ptr_addr(v_expr_4178_);
v___x_4193_ = lean_usize_dec_eq(v___x_4191_, v___x_4192_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; 
lean_inc(v_data_4171_);
lean_dec_ref_known(v_e_4141_, 2);
v___x_4194_ = l_Lean_Expr_mdata___override(v_data_4171_, v_expr_4178_);
v___y_4184_ = v___x_4194_;
goto v___jp_4183_;
}
else
{
lean_dec_ref(v_expr_4178_);
v___y_4184_ = v_e_4141_;
goto v___jp_4183_;
}
v___jp_4183_:
{
lean_object* v___x_4186_; 
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___y_4184_);
v___x_4186_ = v___x_4181_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___y_4184_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_type_x3f_4179_);
v___x_4186_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4188_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4186_);
v___x_4188_ = v___x_4176_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4186_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4141_, 2);
return v___x_4173_;
}
}
case 11:
{
lean_object* v_typeName_4197_; lean_object* v_idx_4198_; lean_object* v_struct_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; 
v_typeName_4197_ = lean_ctor_get(v_e_4141_, 0);
v_idx_4198_ = lean_ctor_get(v_e_4141_, 1);
v_struct_4199_ = lean_ctor_get(v_e_4141_, 2);
lean_inc(v_idx_4198_);
lean_inc(v_typeName_4197_);
lean_inc_ref(v_e_4141_);
lean_inc_ref(v_struct_4199_);
v___f_4200_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4200_, 0, v_struct_4199_);
lean_closure_set(v___f_4200_, 1, v_e_4141_);
lean_closure_set(v___f_4200_, 2, v_typeName_4197_);
lean_closure_set(v___f_4200_, 3, v_idx_4198_);
v___x_4201_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4141_, v___f_4200_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4201_;
}
default: 
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
lean_inc_ref(v_e_4141_);
v___x_4202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4202_, 0, v_e_4141_);
v___x_4203_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4141_, v___x_4202_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4203_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4204_; double v___x_4205_; 
v___x_4204_ = lean_unsigned_to_nat(1000000000u);
v___x_4205_ = lean_float_of_nat(v___x_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_toCold_4214_; lean_object* v_options_4215_; uint8_t v_hasTrace_4216_; 
v_toCold_4214_ = lean_ctor_get(v_a_4211_, 0);
v_options_4215_ = lean_ctor_get(v_toCold_4214_, 2);
v_hasTrace_4216_ = lean_ctor_get_uint8(v_options_4215_, sizeof(void*)*1);
if (v_hasTrace_4216_ == 0)
{
lean_object* v___x_4217_; 
v___x_4217_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
return v___x_4217_;
}
else
{
lean_object* v_inheritedTraceOptions_4218_; lean_object* v___f_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; uint8_t v___x_4223_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v_a_4227_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v_a_4242_; 
v_inheritedTraceOptions_4218_ = lean_ctor_get(v_toCold_4214_, 11);
lean_inc_ref(v_e_4206_);
v___f_4219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4219_, 0, v_e_4206_);
v___x_4220_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4221_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4222_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4218_, v_options_4215_, v___x_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4300_ = l_Lean_trace_profiler;
v___x_4301_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4215_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; 
lean_dec_ref(v___f_4219_);
v___x_4302_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
return v___x_4302_;
}
else
{
goto v___jp_4251_;
}
}
else
{
goto v___jp_4251_;
}
v___jp_4224_:
{
lean_object* v___x_4228_; double v___x_4229_; double v___x_4230_; double v___x_4231_; double v___x_4232_; double v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4228_ = lean_io_mono_nanos_now();
v___x_4229_ = lean_float_of_nat(v___y_4226_);
v___x_4230_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4231_ = lean_float_div(v___x_4229_, v___x_4230_);
v___x_4232_ = lean_float_of_nat(v___x_4228_);
v___x_4233_ = lean_float_div(v___x_4232_, v___x_4230_);
v___x_4234_ = lean_box_float(v___x_4231_);
v___x_4235_ = lean_box_float(v___x_4233_);
v___x_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4234_);
lean_ctor_set(v___x_4236_, 1, v___x_4235_);
v___x_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4237_, 0, v_a_4227_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4220_, v_hasTrace_4216_, v___x_4221_, v_options_4215_, v___x_4223_, v___y_4225_, v___f_4219_, v___x_4237_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
return v___x_4238_;
}
v___jp_4239_:
{
lean_object* v___x_4243_; double v___x_4244_; double v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4243_ = lean_io_get_num_heartbeats();
v___x_4244_ = lean_float_of_nat(v___y_4241_);
v___x_4245_ = lean_float_of_nat(v___x_4243_);
v___x_4246_ = lean_box_float(v___x_4244_);
v___x_4247_ = lean_box_float(v___x_4245_);
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4249_, 0, v_a_4242_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4220_, v_hasTrace_4216_, v___x_4221_, v_options_4215_, v___x_4223_, v___y_4240_, v___f_4219_, v___x_4249_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
return v___x_4250_;
}
v___jp_4251_:
{
lean_object* v___x_4252_; 
v___x_4252_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4212_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v___x_4252_, 1);
v___x_4254_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4255_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4215_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = lean_io_mono_nanos_now();
v___x_4257_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
lean_ctor_set_tag(v___x_4260_, 1);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
v___y_4225_ = v_a_4253_;
v___y_4226_ = v___x_4256_;
v_a_4227_ = v___x_4263_;
goto v___jp_4224_;
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
v_a_4266_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4257_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4257_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set_tag(v___x_4268_, 0);
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
v___y_4225_ = v_a_4253_;
v___y_4226_ = v___x_4256_;
v_a_4227_ = v___x_4271_;
goto v___jp_4224_;
}
}
}
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = lean_io_get_num_heartbeats();
v___x_4275_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set_tag(v___x_4278_, 1);
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
v___y_4240_ = v_a_4253_;
v___y_4241_ = v___x_4274_;
v_a_4242_ = v___x_4281_;
goto v___jp_4239_;
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
v_a_4284_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4275_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4275_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
lean_ctor_set_tag(v___x_4286_, 0);
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
v___y_4240_ = v_a_4253_;
v___y_4241_ = v___x_4274_;
v_a_4242_ = v___x_4289_;
goto v___jp_4239_;
}
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v___f_4219_);
lean_dec_ref(v_e_4206_);
v_a_4292_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4252_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4252_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
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
return v___x_4297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4303_, lean_object* v_e_4304_, lean_object* v_typeName_4305_, lean_object* v_idx_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4303_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4304_, v_typeName_4305_, v_idx_4306_, v_a_4315_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
return v___x_4316_;
}
else
{
lean_dec(v_idx_4306_);
lean_dec(v_typeName_4305_);
lean_dec_ref(v_e_4304_);
return v___x_4314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
lean_dec(v_a_4318_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4326_, lean_object* v_fvars_4327_, lean_object* v_doms_4328_, lean_object* v_e_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4326_, v_fvars_4327_, v_doms_4328_, v_e_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec(v_a_4330_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec(v___y_4339_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4347_, lean_object* v_fvars_4348_, lean_object* v_e_4349_, lean_object* v_letFVars_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4347_, v_fvars_4348_, v_e_4349_, v_letFVars_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
lean_dec(v_a_4356_);
lean_dec_ref(v_a_4355_);
lean_dec(v_a_4354_);
lean_dec_ref(v_a_4353_);
lean_dec(v_a_4352_);
lean_dec(v_a_4351_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4359_, lean_object* v_lctx_4360_, lean_object* v_localInsts_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4360_, v_localInsts_4361_, v_x_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4371_, lean_object* v_lctx_4372_, lean_object* v_localInsts_4373_, lean_object* v_x_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4371_, v_lctx_4372_, v_localInsts_4373_, v_x_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec(v___y_4375_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4383_, lean_object* v_lctx_4384_, lean_object* v_x_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4384_, v_x_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4394_, lean_object* v_lctx_4395_, lean_object* v_x_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4394_, v_lctx_4395_, v_x_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec(v___y_4397_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4410_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec(v___y_4413_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4426_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec(v___y_4429_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4437_, lean_object* v_x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4438_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4447_, lean_object* v_x_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4447_, v_x_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec(v___y_4449_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4457_, lean_object* v_data_4458_, lean_object* v_ref_4459_, lean_object* v_msg_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4457_, v_data_4458_, v_ref_4459_, v_msg_4460_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4469_, lean_object* v_data_4470_, lean_object* v_ref_4471_, lean_object* v_msg_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4469_, v_data_4470_, v_ref_4471_, v_msg_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec(v___y_4473_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(lean_object* v___y_4481_){
_start:
{
lean_object* v___x_4483_; lean_object* v_traceState_4484_; lean_object* v_traces_4485_; lean_object* v___x_4486_; lean_object* v_traceState_4487_; lean_object* v_env_4488_; lean_object* v_nextMacroScope_4489_; lean_object* v_ngen_4490_; lean_object* v_auxDeclNGen_4491_; lean_object* v_cache_4492_; lean_object* v_recordedDeps_4493_; lean_object* v_messages_4494_; lean_object* v_infoState_4495_; lean_object* v_snapshotTasks_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4517_; 
v___x_4483_ = lean_st_ref_get(v___y_4481_);
v_traceState_4484_ = lean_ctor_get(v___x_4483_, 4);
lean_inc_ref(v_traceState_4484_);
lean_dec(v___x_4483_);
v_traces_4485_ = lean_ctor_get(v_traceState_4484_, 0);
lean_inc_ref(v_traces_4485_);
lean_dec_ref(v_traceState_4484_);
v___x_4486_ = lean_st_ref_take(v___y_4481_);
v_traceState_4487_ = lean_ctor_get(v___x_4486_, 4);
v_env_4488_ = lean_ctor_get(v___x_4486_, 0);
v_nextMacroScope_4489_ = lean_ctor_get(v___x_4486_, 1);
v_ngen_4490_ = lean_ctor_get(v___x_4486_, 2);
v_auxDeclNGen_4491_ = lean_ctor_get(v___x_4486_, 3);
v_cache_4492_ = lean_ctor_get(v___x_4486_, 5);
v_recordedDeps_4493_ = lean_ctor_get(v___x_4486_, 6);
v_messages_4494_ = lean_ctor_get(v___x_4486_, 7);
v_infoState_4495_ = lean_ctor_get(v___x_4486_, 8);
v_snapshotTasks_4496_ = lean_ctor_get(v___x_4486_, 9);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4498_ = v___x_4486_;
v_isShared_4499_ = v_isSharedCheck_4517_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_snapshotTasks_4496_);
lean_inc(v_infoState_4495_);
lean_inc(v_messages_4494_);
lean_inc(v_recordedDeps_4493_);
lean_inc(v_cache_4492_);
lean_inc(v_traceState_4487_);
lean_inc(v_auxDeclNGen_4491_);
lean_inc(v_ngen_4490_);
lean_inc(v_nextMacroScope_4489_);
lean_inc(v_env_4488_);
lean_dec(v___x_4486_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4517_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
uint64_t v_tid_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4515_; 
v_tid_4500_ = lean_ctor_get_uint64(v_traceState_4487_, sizeof(void*)*1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_traceState_4487_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v_traceState_4487_, 0);
lean_dec(v_unused_4516_);
v___x_4502_ = v_traceState_4487_;
v_isShared_4503_ = v_isSharedCheck_4515_;
goto v_resetjp_4501_;
}
else
{
lean_dec(v_traceState_4487_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4515_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4504_ = lean_unsigned_to_nat(32u);
v___x_4505_ = lean_mk_empty_array_with_capacity(v___x_4504_);
lean_dec_ref(v___x_4505_);
v___x_4506_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4506_);
v___x_4508_ = v___x_4502_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4506_);
lean_ctor_set_uint64(v_reuseFailAlloc_4514_, sizeof(void*)*1, v_tid_4500_);
v___x_4508_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 4, v___x_4508_);
v___x_4510_ = v___x_4498_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_env_4488_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_nextMacroScope_4489_);
lean_ctor_set(v_reuseFailAlloc_4513_, 2, v_ngen_4490_);
lean_ctor_set(v_reuseFailAlloc_4513_, 3, v_auxDeclNGen_4491_);
lean_ctor_set(v_reuseFailAlloc_4513_, 4, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4513_, 5, v_cache_4492_);
lean_ctor_set(v_reuseFailAlloc_4513_, 6, v_recordedDeps_4493_);
lean_ctor_set(v_reuseFailAlloc_4513_, 7, v_messages_4494_);
lean_ctor_set(v_reuseFailAlloc_4513_, 8, v_infoState_4495_);
lean_ctor_set(v_reuseFailAlloc_4513_, 9, v_snapshotTasks_4496_);
v___x_4510_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = lean_st_ref_put(v___y_4481_, v___x_4510_);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v_traces_4485_);
return v___x_4512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg___boxed(lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v___y_4518_);
lean_dec(v___y_4518_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v___x_4526_; 
v___x_4526_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v___y_4524_);
return v___x_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4533_, lean_object* v_msg_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_ref_4540_; lean_object* v___x_4541_; lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4587_; 
v_ref_4540_ = lean_ctor_get(v___y_4537_, 2);
v___x_4541_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4544_ = v___x_4541_;
v_isShared_4545_ = v_isSharedCheck_4587_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4541_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4587_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4546_; lean_object* v_traceState_4547_; lean_object* v_env_4548_; lean_object* v_nextMacroScope_4549_; lean_object* v_ngen_4550_; lean_object* v_auxDeclNGen_4551_; lean_object* v_cache_4552_; lean_object* v_recordedDeps_4553_; lean_object* v_messages_4554_; lean_object* v_infoState_4555_; lean_object* v_snapshotTasks_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4586_; 
v___x_4546_ = lean_st_ref_take(v___y_4538_);
v_traceState_4547_ = lean_ctor_get(v___x_4546_, 4);
v_env_4548_ = lean_ctor_get(v___x_4546_, 0);
v_nextMacroScope_4549_ = lean_ctor_get(v___x_4546_, 1);
v_ngen_4550_ = lean_ctor_get(v___x_4546_, 2);
v_auxDeclNGen_4551_ = lean_ctor_get(v___x_4546_, 3);
v_cache_4552_ = lean_ctor_get(v___x_4546_, 5);
v_recordedDeps_4553_ = lean_ctor_get(v___x_4546_, 6);
v_messages_4554_ = lean_ctor_get(v___x_4546_, 7);
v_infoState_4555_ = lean_ctor_get(v___x_4546_, 8);
v_snapshotTasks_4556_ = lean_ctor_get(v___x_4546_, 9);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4558_ = v___x_4546_;
v_isShared_4559_ = v_isSharedCheck_4586_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_snapshotTasks_4556_);
lean_inc(v_infoState_4555_);
lean_inc(v_messages_4554_);
lean_inc(v_recordedDeps_4553_);
lean_inc(v_cache_4552_);
lean_inc(v_traceState_4547_);
lean_inc(v_auxDeclNGen_4551_);
lean_inc(v_ngen_4550_);
lean_inc(v_nextMacroScope_4549_);
lean_inc(v_env_4548_);
lean_dec(v___x_4546_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4586_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
uint64_t v_tid_4560_; lean_object* v_traces_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4585_; 
v_tid_4560_ = lean_ctor_get_uint64(v_traceState_4547_, sizeof(void*)*1);
v_traces_4561_ = lean_ctor_get(v_traceState_4547_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_traceState_4547_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4563_ = v_traceState_4547_;
v_isShared_4564_ = v_isSharedCheck_4585_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_traces_4561_);
lean_dec(v_traceState_4547_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4585_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; double v___x_4567_; uint8_t v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4576_; 
v___x_4565_ = lean_box(0);
v___x_4566_ = lean_box(0);
v___x_4567_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4568_ = 0;
v___x_4569_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4570_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4570_, 0, v_cls_4533_);
lean_ctor_set(v___x_4570_, 1, v___x_4566_);
lean_ctor_set(v___x_4570_, 2, v___x_4569_);
lean_ctor_set_float(v___x_4570_, sizeof(void*)*3, v___x_4567_);
lean_ctor_set_float(v___x_4570_, sizeof(void*)*3 + 8, v___x_4567_);
lean_ctor_set_uint8(v___x_4570_, sizeof(void*)*3 + 16, v___x_4568_);
v___x_4571_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4572_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4570_);
lean_ctor_set(v___x_4572_, 1, v_a_4542_);
lean_ctor_set(v___x_4572_, 2, v___x_4571_);
lean_inc(v_ref_4540_);
v___x_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4573_, 0, v_ref_4540_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = l_Lean_PersistentArray_push___redArg(v_traces_4561_, v___x_4573_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4574_);
v___x_4576_ = v___x_4563_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4574_);
lean_ctor_set_uint64(v_reuseFailAlloc_4584_, sizeof(void*)*1, v_tid_4560_);
v___x_4576_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
lean_object* v___x_4578_; 
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 4, v___x_4576_);
v___x_4578_ = v___x_4558_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_env_4548_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_nextMacroScope_4549_);
lean_ctor_set(v_reuseFailAlloc_4583_, 2, v_ngen_4550_);
lean_ctor_set(v_reuseFailAlloc_4583_, 3, v_auxDeclNGen_4551_);
lean_ctor_set(v_reuseFailAlloc_4583_, 4, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4583_, 5, v_cache_4552_);
lean_ctor_set(v_reuseFailAlloc_4583_, 6, v_recordedDeps_4553_);
lean_ctor_set(v_reuseFailAlloc_4583_, 7, v_messages_4554_);
lean_ctor_set(v_reuseFailAlloc_4583_, 8, v_infoState_4555_);
lean_ctor_set(v_reuseFailAlloc_4583_, 9, v_snapshotTasks_4556_);
v___x_4578_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4579_ = lean_st_ref_put(v___y_4538_, v___x_4578_);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v___x_4565_);
v___x_4581_ = v___x_4544_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4565_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4588_, lean_object* v_msg_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4588_, v_msg_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
return v_res_4595_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0));
v___x_4598_ = l_Lean_stringToMessageData(v___x_4597_);
return v___x_4598_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4600_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2));
v___x_4601_ = l_Lean_stringToMessageData(v___x_4600_);
return v___x_4601_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4603_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4));
v___x_4604_ = l_Lean_stringToMessageData(v___x_4603_);
return v___x_4604_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6));
v___x_4607_ = l_Lean_stringToMessageData(v___x_4606_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___x_4608_, lean_object* v_e_4609_, lean_object* v___x_4610_, lean_object* v___x_4611_, lean_object* v_cls_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = lean_st_mk_ref(v___x_4608_);
v___x_4619_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4609_, v___x_4610_, v___x_4618_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4691_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4622_ = v___x_4619_;
v_isShared_4623_ = v_isSharedCheck_4691_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4619_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4691_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4624_; lean_object* v_count_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4689_; 
v___x_4624_ = lean_st_ref_get(v___x_4618_);
lean_dec(v___x_4618_);
v_count_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4689_ == 0)
{
lean_object* v_unused_4690_; 
v_unused_4690_ = lean_ctor_get(v___x_4624_, 1);
lean_dec(v_unused_4690_);
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4689_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_count_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4689_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
uint8_t v___x_4651_; 
v___x_4651_ = lean_nat_dec_eq(v_count_4625_, v___x_4611_);
if (v___x_4651_ == 0)
{
lean_object* v_toCold_4652_; lean_object* v_options_4653_; uint8_t v_hasTrace_4654_; 
v_toCold_4652_ = lean_ctor_get(v___y_4615_, 0);
v_options_4653_ = lean_ctor_get(v_toCold_4652_, 2);
v_hasTrace_4654_ = lean_ctor_get_uint8(v_options_4653_, sizeof(void*)*1);
if (v_hasTrace_4654_ == 0)
{
lean_dec(v_cls_4612_);
goto v___jp_4629_;
}
else
{
lean_object* v_inheritedTraceOptions_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; 
v_inheritedTraceOptions_4655_ = lean_ctor_get(v_toCold_4652_, 11);
v___x_4656_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4612_);
v___x_4657_ = l_Lean_Name_append(v___x_4656_, v_cls_4612_);
v___x_4658_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4655_, v_options_4653_, v___x_4657_);
lean_dec(v___x_4657_);
if (v___x_4658_ == 0)
{
lean_dec(v_cls_4612_);
goto v___jp_4629_;
}
else
{
lean_object* v_expr_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v_expr_4659_ = lean_ctor_get(v_a_4620_, 0);
v___x_4660_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5);
lean_inc_ref(v_expr_4659_);
v___x_4661_ = l_Lean_indentExpr(v_expr_4659_);
v___x_4662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4660_);
lean_ctor_set(v___x_4662_, 1, v___x_4661_);
v___x_4663_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4612_, v___x_4662_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_dec_ref_known(v___x_4663_, 1);
goto v___jp_4629_;
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_del_object(v___x_4627_);
lean_dec(v_count_4625_);
lean_del_object(v___x_4622_);
lean_dec(v_a_4620_);
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4672_; lean_object* v_options_4673_; uint8_t v_hasTrace_4674_; 
v_toCold_4672_ = lean_ctor_get(v___y_4615_, 0);
v_options_4673_ = lean_ctor_get(v_toCold_4672_, 2);
v_hasTrace_4674_ = lean_ctor_get_uint8(v_options_4673_, sizeof(void*)*1);
if (v_hasTrace_4674_ == 0)
{
lean_dec(v_cls_4612_);
goto v___jp_4629_;
}
else
{
lean_object* v_inheritedTraceOptions_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_inheritedTraceOptions_4675_ = lean_ctor_get(v_toCold_4672_, 11);
v___x_4676_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4612_);
v___x_4677_ = l_Lean_Name_append(v___x_4676_, v_cls_4612_);
v___x_4678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4675_, v_options_4673_, v___x_4677_);
lean_dec(v___x_4677_);
if (v___x_4678_ == 0)
{
lean_dec(v_cls_4612_);
goto v___jp_4629_;
}
else
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7);
v___x_4680_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4612_, v___x_4679_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_dec_ref_known(v___x_4680_, 1);
goto v___jp_4629_;
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
lean_del_object(v___x_4627_);
lean_dec(v_count_4625_);
lean_del_object(v___x_4622_);
lean_dec(v_a_4620_);
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
v___jp_4629_:
{
lean_object* v_expr_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4649_; 
v_expr_4630_ = lean_ctor_get(v_a_4620_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v_a_4620_);
if (v_isSharedCheck_4649_ == 0)
{
lean_object* v_unused_4650_; 
v_unused_4650_ = lean_ctor_get(v_a_4620_, 1);
lean_dec(v_unused_4650_);
v___x_4632_ = v_a_4620_;
v_isShared_4633_ = v_isSharedCheck_4649_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_expr_4630_);
lean_dec(v_a_4620_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4649_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4639_; 
v___x_4634_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1);
v___x_4635_ = l_Nat_reprFast(v_count_4625_);
v___x_4636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
v___x_4637_ = l_Lean_MessageData_ofFormat(v___x_4636_);
if (v_isShared_4633_ == 0)
{
lean_ctor_set_tag(v___x_4632_, 7);
lean_ctor_set(v___x_4632_, 1, v___x_4637_);
lean_ctor_set(v___x_4632_, 0, v___x_4634_);
v___x_4639_ = v___x_4632_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v___x_4637_);
v___x_4639_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
lean_object* v___x_4640_; lean_object* v___x_4642_; 
v___x_4640_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3);
if (v_isShared_4628_ == 0)
{
lean_ctor_set_tag(v___x_4627_, 7);
lean_ctor_set(v___x_4627_, 1, v___x_4640_);
lean_ctor_set(v___x_4627_, 0, v___x_4639_);
v___x_4642_ = v___x_4627_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4647_, 1, v___x_4640_);
v___x_4642_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4643_; lean_object* v___x_4645_; 
v___x_4643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4643_, 0, v_expr_4630_);
lean_ctor_set(v___x_4643_, 1, v___x_4642_);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 0, v___x_4643_);
v___x_4645_ = v___x_4622_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
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
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
lean_dec(v___x_4618_);
lean_dec(v_cls_4612_);
v_a_4692_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4619_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4619_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___x_4700_, lean_object* v_e_4701_, lean_object* v___x_4702_, lean_object* v___x_4703_, lean_object* v_cls_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___x_4700_, v_e_4701_, v___x_4702_, v___x_4703_, v_cls_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___x_4703_);
lean_dec(v___x_4702_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(uint8_t v___x_4711_, lean_object* v___f_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v___x_4763_; uint8_t v_beta_4764_; 
v___x_4763_ = l_Lean_Meta_Context_config(v___y_4713_);
v_beta_4764_ = lean_ctor_get_uint8(v___x_4763_, 13);
if (v_beta_4764_ == 0)
{
lean_dec_ref(v___x_4763_);
goto v___jp_4718_;
}
else
{
uint8_t v_iota_4765_; 
v_iota_4765_ = lean_ctor_get_uint8(v___x_4763_, 12);
if (v_iota_4765_ == 0)
{
lean_dec_ref(v___x_4763_);
goto v___jp_4718_;
}
else
{
uint8_t v_zeta_4766_; 
v_zeta_4766_ = lean_ctor_get_uint8(v___x_4763_, 15);
if (v_zeta_4766_ == 0)
{
lean_dec_ref(v___x_4763_);
goto v___jp_4718_;
}
else
{
uint8_t v_zetaHave_4767_; 
v_zetaHave_4767_ = lean_ctor_get_uint8(v___x_4763_, 18);
if (v_zetaHave_4767_ == 0)
{
lean_dec_ref(v___x_4763_);
goto v___jp_4718_;
}
else
{
uint8_t v_zetaDelta_4768_; 
v_zetaDelta_4768_ = lean_ctor_get_uint8(v___x_4763_, 16);
if (v_zetaDelta_4768_ == 0)
{
lean_dec_ref(v___x_4763_);
goto v___jp_4718_;
}
else
{
uint8_t v_etaStruct_4769_; uint8_t v_proj_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; 
v_etaStruct_4769_ = lean_ctor_get_uint8(v___x_4763_, 10);
v_proj_4770_ = lean_ctor_get_uint8(v___x_4763_, 14);
lean_dec_ref(v___x_4763_);
v___x_4771_ = lean_box(v_proj_4770_);
v___x_4772_ = lean_obj_tag_nat(v___x_4771_);
lean_dec(v___x_4771_);
v___x_4773_ = lean_unsigned_to_nat(2u);
v___x_4774_ = lean_nat_dec_eq(v___x_4772_, v___x_4773_);
if (v___x_4774_ == 0)
{
goto v___jp_4718_;
}
else
{
uint8_t v___x_4775_; uint8_t v___x_4776_; 
v___x_4775_ = 0;
v___x_4776_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4769_, v___x_4775_);
if (v___x_4776_ == 0)
{
goto v___jp_4718_;
}
else
{
lean_object* v___x_4777_; 
v___x_4777_ = lean_apply_5(v___f_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, lean_box(0));
return v___x_4777_;
}
}
}
}
}
}
}
v___jp_4718_:
{
lean_object* v___x_4719_; uint8_t v_foApprox_4720_; uint8_t v_ctxApprox_4721_; uint8_t v_quasiPatternApprox_4722_; uint8_t v_constApprox_4723_; uint8_t v_isDefEqStuckEx_4724_; uint8_t v_unificationHints_4725_; uint8_t v_proofIrrelevance_4726_; uint8_t v_assignSyntheticOpaque_4727_; uint8_t v_offsetCnstrs_4728_; uint8_t v_transparency_4729_; uint8_t v_univApprox_4730_; uint8_t v_zetaUnused_4731_; uint8_t v_canUnfoldPredicateConfig_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4762_; 
v___x_4719_ = l_Lean_Meta_Context_config(v___y_4713_);
v_foApprox_4720_ = lean_ctor_get_uint8(v___x_4719_, 0);
v_ctxApprox_4721_ = lean_ctor_get_uint8(v___x_4719_, 1);
v_quasiPatternApprox_4722_ = lean_ctor_get_uint8(v___x_4719_, 2);
v_constApprox_4723_ = lean_ctor_get_uint8(v___x_4719_, 3);
v_isDefEqStuckEx_4724_ = lean_ctor_get_uint8(v___x_4719_, 4);
v_unificationHints_4725_ = lean_ctor_get_uint8(v___x_4719_, 5);
v_proofIrrelevance_4726_ = lean_ctor_get_uint8(v___x_4719_, 6);
v_assignSyntheticOpaque_4727_ = lean_ctor_get_uint8(v___x_4719_, 7);
v_offsetCnstrs_4728_ = lean_ctor_get_uint8(v___x_4719_, 8);
v_transparency_4729_ = lean_ctor_get_uint8(v___x_4719_, 9);
v_univApprox_4730_ = lean_ctor_get_uint8(v___x_4719_, 11);
v_zetaUnused_4731_ = lean_ctor_get_uint8(v___x_4719_, 17);
v_canUnfoldPredicateConfig_4732_ = lean_ctor_get_uint8(v___x_4719_, 19);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4734_ = v___x_4719_;
v_isShared_4735_ = v_isSharedCheck_4762_;
goto v_resetjp_4733_;
}
else
{
lean_dec(v___x_4719_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4762_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
uint8_t v___x_4736_; uint8_t v___x_4737_; lean_object* v___x_4739_; 
v___x_4736_ = 0;
v___x_4737_ = 2;
if (v_isShared_4735_ == 0)
{
v___x_4739_ = v___x_4734_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 0, v_foApprox_4720_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 1, v_ctxApprox_4721_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 2, v_quasiPatternApprox_4722_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 3, v_constApprox_4723_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 4, v_isDefEqStuckEx_4724_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 5, v_unificationHints_4725_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 6, v_proofIrrelevance_4726_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 7, v_assignSyntheticOpaque_4727_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 8, v_offsetCnstrs_4728_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 9, v_transparency_4729_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 11, v_univApprox_4730_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 17, v_zetaUnused_4731_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, 19, v_canUnfoldPredicateConfig_4732_);
v___x_4739_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
uint8_t v_trackZetaDelta_4740_; lean_object* v_zetaDeltaSet_4741_; lean_object* v_lctx_4742_; lean_object* v_localInstances_4743_; lean_object* v_defEqCtx_x3f_4744_; lean_object* v_synthPendingDepth_4745_; lean_object* v_customCanUnfoldPredicate_x3f_4746_; uint8_t v_univApprox_4747_; uint8_t v_inTypeClassResolution_4748_; uint8_t v_cacheInferType_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4759_; 
lean_ctor_set_uint8(v___x_4739_, 10, v___x_4736_);
lean_ctor_set_uint8(v___x_4739_, 12, v___x_4711_);
lean_ctor_set_uint8(v___x_4739_, 13, v___x_4711_);
lean_ctor_set_uint8(v___x_4739_, 14, v___x_4737_);
lean_ctor_set_uint8(v___x_4739_, 15, v___x_4711_);
lean_ctor_set_uint8(v___x_4739_, 16, v___x_4711_);
lean_ctor_set_uint8(v___x_4739_, 18, v___x_4711_);
v_trackZetaDelta_4740_ = lean_ctor_get_uint8(v___y_4713_, sizeof(void*)*7);
v_zetaDeltaSet_4741_ = lean_ctor_get(v___y_4713_, 1);
v_lctx_4742_ = lean_ctor_get(v___y_4713_, 2);
v_localInstances_4743_ = lean_ctor_get(v___y_4713_, 3);
v_defEqCtx_x3f_4744_ = lean_ctor_get(v___y_4713_, 4);
v_synthPendingDepth_4745_ = lean_ctor_get(v___y_4713_, 5);
v_customCanUnfoldPredicate_x3f_4746_ = lean_ctor_get(v___y_4713_, 6);
v_univApprox_4747_ = lean_ctor_get_uint8(v___y_4713_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4748_ = lean_ctor_get_uint8(v___y_4713_, sizeof(void*)*7 + 2);
v_cacheInferType_4749_ = lean_ctor_get_uint8(v___y_4713_, sizeof(void*)*7 + 3);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___y_4713_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; 
v_unused_4760_ = lean_ctor_get(v___y_4713_, 0);
lean_dec(v_unused_4760_);
v___x_4751_ = v___y_4713_;
v_isShared_4752_ = v_isSharedCheck_4759_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4746_);
lean_inc(v_synthPendingDepth_4745_);
lean_inc(v_defEqCtx_x3f_4744_);
lean_inc(v_localInstances_4743_);
lean_inc(v_lctx_4742_);
lean_inc(v_zetaDeltaSet_4741_);
lean_dec(v___y_4713_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4759_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
uint64_t v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4753_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4739_);
v___x_4754_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4754_, 0, v___x_4739_);
lean_ctor_set_uint64(v___x_4754_, sizeof(void*)*1, v___x_4753_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4754_);
v___x_4756_ = v___x_4751_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4754_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_zetaDeltaSet_4741_);
lean_ctor_set(v_reuseFailAlloc_4758_, 2, v_lctx_4742_);
lean_ctor_set(v_reuseFailAlloc_4758_, 3, v_localInstances_4743_);
lean_ctor_set(v_reuseFailAlloc_4758_, 4, v_defEqCtx_x3f_4744_);
lean_ctor_set(v_reuseFailAlloc_4758_, 5, v_synthPendingDepth_4745_);
lean_ctor_set(v_reuseFailAlloc_4758_, 6, v_customCanUnfoldPredicate_x3f_4746_);
lean_ctor_set_uint8(v_reuseFailAlloc_4758_, sizeof(void*)*7, v_trackZetaDelta_4740_);
lean_ctor_set_uint8(v_reuseFailAlloc_4758_, sizeof(void*)*7 + 1, v_univApprox_4747_);
lean_ctor_set_uint8(v_reuseFailAlloc_4758_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4748_);
lean_ctor_set_uint8(v_reuseFailAlloc_4758_, sizeof(void*)*7 + 3, v_cacheInferType_4749_);
v___x_4756_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
lean_object* v___x_4757_; 
v___x_4757_ = lean_apply_5(v___f_4712_, v___x_4756_, v___y_4714_, v___y_4715_, v___y_4716_, lean_box(0));
return v___x_4757_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4778_, lean_object* v___f_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
uint8_t v___x_14148__boxed_4785_; lean_object* v_res_4786_; 
v___x_14148__boxed_4785_ = lean_unbox(v___x_4778_);
v_res_4786_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_14148__boxed_4785_, v___f_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4787_, lean_object* v_cache_4788_, lean_object* v_a_x3f_4789_){
_start:
{
lean_object* v___x_4791_; lean_object* v_mctx_4792_; lean_object* v_zetaDeltaFVarIds_4793_; lean_object* v_postponed_4794_; lean_object* v_diag_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4805_; 
v___x_4791_ = lean_st_ref_take(v___y_4787_);
v_mctx_4792_ = lean_ctor_get(v___x_4791_, 0);
v_zetaDeltaFVarIds_4793_ = lean_ctor_get(v___x_4791_, 2);
v_postponed_4794_ = lean_ctor_get(v___x_4791_, 3);
v_diag_4795_ = lean_ctor_get(v___x_4791_, 4);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4805_ == 0)
{
lean_object* v_unused_4806_; 
v_unused_4806_ = lean_ctor_get(v___x_4791_, 1);
lean_dec(v_unused_4806_);
v___x_4797_ = v___x_4791_;
v_isShared_4798_ = v_isSharedCheck_4805_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_diag_4795_);
lean_inc(v_postponed_4794_);
lean_inc(v_zetaDeltaFVarIds_4793_);
lean_inc(v_mctx_4792_);
lean_dec(v___x_4791_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4805_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4799_ = lean_box(0);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 1, v_cache_4788_);
v___x_4801_ = v___x_4797_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_mctx_4792_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_cache_4788_);
lean_ctor_set(v_reuseFailAlloc_4804_, 2, v_zetaDeltaFVarIds_4793_);
lean_ctor_set(v_reuseFailAlloc_4804_, 3, v_postponed_4794_);
lean_ctor_set(v_reuseFailAlloc_4804_, 4, v_diag_4795_);
v___x_4801_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4802_ = lean_st_ref_put(v___y_4787_, v___x_4801_);
v___x_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4799_);
return v___x_4803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4807_, lean_object* v_cache_4808_, lean_object* v_a_x3f_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4807_, v_cache_4808_, v_a_x3f_4809_);
lean_dec(v_a_x3f_4809_);
lean_dec(v___y_4807_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(lean_object* v___y_4812_, lean_object* v_zetaDeltaFVarIds_4813_, lean_object* v_a_x3f_4814_){
_start:
{
lean_object* v___x_4816_; lean_object* v_mctx_4817_; lean_object* v_cache_4818_; lean_object* v_postponed_4819_; lean_object* v_diag_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4830_; 
v___x_4816_ = lean_st_ref_take(v___y_4812_);
v_mctx_4817_ = lean_ctor_get(v___x_4816_, 0);
v_cache_4818_ = lean_ctor_get(v___x_4816_, 1);
v_postponed_4819_ = lean_ctor_get(v___x_4816_, 3);
v_diag_4820_ = lean_ctor_get(v___x_4816_, 4);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4830_ == 0)
{
lean_object* v_unused_4831_; 
v_unused_4831_ = lean_ctor_get(v___x_4816_, 2);
lean_dec(v_unused_4831_);
v___x_4822_ = v___x_4816_;
v_isShared_4823_ = v_isSharedCheck_4830_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_diag_4820_);
lean_inc(v_postponed_4819_);
lean_inc(v_cache_4818_);
lean_inc(v_mctx_4817_);
lean_dec(v___x_4816_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4830_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4824_; lean_object* v___x_4826_; 
v___x_4824_ = lean_box(0);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 2, v_zetaDeltaFVarIds_4813_);
v___x_4826_ = v___x_4822_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_mctx_4817_);
lean_ctor_set(v_reuseFailAlloc_4829_, 1, v_cache_4818_);
lean_ctor_set(v_reuseFailAlloc_4829_, 2, v_zetaDeltaFVarIds_4813_);
lean_ctor_set(v_reuseFailAlloc_4829_, 3, v_postponed_4819_);
lean_ctor_set(v_reuseFailAlloc_4829_, 4, v_diag_4820_);
v___x_4826_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_st_ref_put(v___y_4812_, v___x_4826_);
v___x_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4824_);
return v___x_4828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___y_4832_, lean_object* v_zetaDeltaFVarIds_4833_, lean_object* v_a_x3f_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4832_, v_zetaDeltaFVarIds_4833_, v_a_x3f_4834_);
lean_dec(v_a_x3f_4834_);
lean_dec(v___y_4832_);
return v_res_4836_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg(){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___boxed(lean_object* v___dummy_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg();
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
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4848_ = lean_box(0);
v___x_4849_ = lean_unsigned_to_nat(16u);
v___x_4850_ = lean_mk_array(v___x_4849_, v___x_4848_);
return v___x_4850_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___x_4852_ = lean_unsigned_to_nat(0u);
v___x_4853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
lean_ctor_set(v___x_4853_, 1, v___x_4851_);
return v___x_4853_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4854_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4855_ = lean_unsigned_to_nat(0u);
v___x_4856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
lean_ctor_set(v___x_4856_, 1, v___x_4854_);
return v___x_4856_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6(void){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg();
return v___x_4857_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7(void){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4858_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
return v___x_4859_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4860_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7);
v___x_4861_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
v___x_4862_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set(v___x_4862_, 1, v___x_4860_);
lean_ctor_set(v___x_4862_, 2, v___x_4860_);
lean_ctor_set(v___x_4862_, 3, v___x_4860_);
lean_ctor_set(v___x_4862_, 4, v___x_4860_);
lean_ctor_set(v___x_4862_, 5, v___x_4860_);
lean_ctor_set(v___x_4862_, 6, v___x_4860_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_4863_, lean_object* v_e_4864_, lean_object* v_cls_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
if (v___x_4863_ == 0)
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
lean_dec(v_cls_4865_);
v___x_4871_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_4872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4872_, 0, v_e_4864_);
lean_ctor_set(v___x_4872_, 1, v___x_4871_);
v___x_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
return v___x_4873_;
}
else
{
uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___f_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v_cache_4881_; lean_object* v_a_4883_; lean_object* v___x_4894_; lean_object* v_mctx_4895_; lean_object* v_zetaDeltaFVarIds_4896_; lean_object* v_postponed_4897_; lean_object* v_diag_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4976_; 
v___x_4874_ = 0;
v___x_4875_ = lean_box(0);
v___x_4876_ = lean_unsigned_to_nat(0u);
v___x_4877_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
v___f_4878_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4878_, 0, v___x_4877_);
lean_closure_set(v___f_4878_, 1, v_e_4864_);
lean_closure_set(v___f_4878_, 2, v___x_4875_);
lean_closure_set(v___f_4878_, 3, v___x_4876_);
lean_closure_set(v___f_4878_, 4, v_cls_4865_);
v___x_4879_ = lean_box(1);
v___x_4880_ = lean_st_ref_get(v___y_4867_);
v_cache_4881_ = lean_ctor_get(v___x_4880_, 1);
lean_inc_ref(v_cache_4881_);
lean_dec(v___x_4880_);
v___x_4894_ = lean_st_ref_take(v___y_4867_);
v_mctx_4895_ = lean_ctor_get(v___x_4894_, 0);
v_zetaDeltaFVarIds_4896_ = lean_ctor_get(v___x_4894_, 2);
v_postponed_4897_ = lean_ctor_get(v___x_4894_, 3);
v_diag_4898_ = lean_ctor_get(v___x_4894_, 4);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4976_ == 0)
{
lean_object* v_unused_4977_; 
v_unused_4977_ = lean_ctor_get(v___x_4894_, 1);
lean_dec(v_unused_4977_);
v___x_4900_ = v___x_4894_;
v_isShared_4901_ = v_isSharedCheck_4976_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_diag_4898_);
lean_inc(v_postponed_4897_);
lean_inc(v_zetaDeltaFVarIds_4896_);
lean_inc(v_mctx_4895_);
lean_dec(v___x_4894_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4976_;
goto v_resetjp_4899_;
}
v___jp_4882_:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
v___x_4884_ = lean_box(0);
v___x_4885_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4867_, v_cache_4881_, v___x_4884_);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4892_ == 0)
{
lean_object* v_unused_4893_; 
v_unused_4893_ = lean_ctor_get(v___x_4885_, 0);
lean_dec(v_unused_4893_);
v___x_4887_ = v___x_4885_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_dec(v___x_4885_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
lean_ctor_set_tag(v___x_4887_, 1);
lean_ctor_set(v___x_4887_, 0, v_a_4883_);
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4883_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
v_resetjp_4899_:
{
lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4902_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v___x_4902_);
v___x_4904_ = v___x_4900_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_mctx_4895_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v___x_4902_);
lean_ctor_set(v_reuseFailAlloc_4975_, 2, v_zetaDeltaFVarIds_4896_);
lean_ctor_set(v_reuseFailAlloc_4975_, 3, v_postponed_4897_);
lean_ctor_set(v_reuseFailAlloc_4975_, 4, v_diag_4898_);
v___x_4904_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4905_; lean_object* v_keyedConfig_4906_; lean_object* v_zetaDeltaSet_4907_; lean_object* v_lctx_4908_; lean_object* v_localInstances_4909_; lean_object* v_defEqCtx_x3f_4910_; lean_object* v_synthPendingDepth_4911_; lean_object* v_customCanUnfoldPredicate_x3f_4912_; uint8_t v_univApprox_4913_; uint8_t v_inTypeClassResolution_4914_; uint8_t v_cacheInferType_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v_mctx_4918_; lean_object* v_cache_4919_; lean_object* v_zetaDeltaFVarIds_4920_; lean_object* v_postponed_4921_; lean_object* v_diag_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4974_; 
v___x_4905_ = lean_st_ref_put(v___y_4867_, v___x_4904_);
v_keyedConfig_4906_ = lean_ctor_get(v___y_4866_, 0);
v_zetaDeltaSet_4907_ = lean_ctor_get(v___y_4866_, 1);
v_lctx_4908_ = lean_ctor_get(v___y_4866_, 2);
v_localInstances_4909_ = lean_ctor_get(v___y_4866_, 3);
v_defEqCtx_x3f_4910_ = lean_ctor_get(v___y_4866_, 4);
v_synthPendingDepth_4911_ = lean_ctor_get(v___y_4866_, 5);
v_customCanUnfoldPredicate_x3f_4912_ = lean_ctor_get(v___y_4866_, 6);
v_univApprox_4913_ = lean_ctor_get_uint8(v___y_4866_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4914_ = lean_ctor_get_uint8(v___y_4866_, sizeof(void*)*7 + 2);
v_cacheInferType_4915_ = lean_ctor_get_uint8(v___y_4866_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_4912_);
lean_inc(v_synthPendingDepth_4911_);
lean_inc(v_defEqCtx_x3f_4910_);
lean_inc_ref(v_localInstances_4909_);
lean_inc_ref(v_lctx_4908_);
lean_inc(v_zetaDeltaSet_4907_);
lean_inc_ref(v_keyedConfig_4906_);
v___x_4916_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4916_, 0, v_keyedConfig_4906_);
lean_ctor_set(v___x_4916_, 1, v_zetaDeltaSet_4907_);
lean_ctor_set(v___x_4916_, 2, v_lctx_4908_);
lean_ctor_set(v___x_4916_, 3, v_localInstances_4909_);
lean_ctor_set(v___x_4916_, 4, v_defEqCtx_x3f_4910_);
lean_ctor_set(v___x_4916_, 5, v_synthPendingDepth_4911_);
lean_ctor_set(v___x_4916_, 6, v_customCanUnfoldPredicate_x3f_4912_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*7, v___x_4863_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*7 + 1, v_univApprox_4913_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4914_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*7 + 3, v_cacheInferType_4915_);
v___x_4917_ = lean_st_ref_take(v___y_4867_);
v_mctx_4918_ = lean_ctor_get(v___x_4917_, 0);
v_cache_4919_ = lean_ctor_get(v___x_4917_, 1);
v_zetaDeltaFVarIds_4920_ = lean_ctor_get(v___x_4917_, 2);
v_postponed_4921_ = lean_ctor_get(v___x_4917_, 3);
v_diag_4922_ = lean_ctor_get(v___x_4917_, 4);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4924_ = v___x_4917_;
v_isShared_4925_ = v_isSharedCheck_4974_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_diag_4922_);
lean_inc(v_postponed_4921_);
lean_inc(v_zetaDeltaFVarIds_4920_);
lean_inc(v_cache_4919_);
lean_inc(v_mctx_4918_);
lean_dec(v___x_4917_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4974_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v_a_4927_; lean_object* v_a_4931_; lean_object* v___y_4944_; lean_object* v___y_4948_; lean_object* v___x_4952_; 
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 2, v___x_4879_);
v___x_4952_ = v___x_4924_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_mctx_4918_);
lean_ctor_set(v_reuseFailAlloc_4973_, 1, v_cache_4919_);
lean_ctor_set(v_reuseFailAlloc_4973_, 2, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4973_, 3, v_postponed_4921_);
lean_ctor_set(v_reuseFailAlloc_4973_, 4, v_diag_4922_);
v___x_4952_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4951_;
}
v___jp_4926_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4928_ = lean_box(0);
v___x_4929_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4867_, v_zetaDeltaFVarIds_4920_, v___x_4928_);
lean_dec_ref(v___x_4929_);
v_a_4883_ = v_a_4927_;
goto v___jp_4882_;
}
v___jp_4930_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
lean_inc(v_a_4931_);
v___x_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4932_, 0, v_a_4931_);
v___x_4933_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4867_, v_zetaDeltaFVarIds_4920_, v___x_4932_);
lean_dec_ref(v___x_4933_);
v___x_4934_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4867_, v_cache_4881_, v___x_4932_);
lean_dec_ref_known(v___x_4932_, 1);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4941_ == 0)
{
lean_object* v_unused_4942_; 
v_unused_4942_ = lean_ctor_get(v___x_4934_, 0);
lean_dec(v_unused_4942_);
v___x_4936_ = v___x_4934_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_dec(v___x_4934_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v_a_4931_);
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4931_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
v___jp_4943_:
{
if (lean_obj_tag(v___y_4944_) == 0)
{
lean_object* v_a_4945_; 
v_a_4945_ = lean_ctor_get(v___y_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v___y_4944_, 1);
v_a_4931_ = v_a_4945_;
goto v___jp_4930_;
}
else
{
lean_object* v_a_4946_; 
v_a_4946_ = lean_ctor_get(v___y_4944_, 0);
lean_inc(v_a_4946_);
lean_dec_ref_known(v___y_4944_, 1);
v_a_4927_ = v_a_4946_;
goto v___jp_4926_;
}
}
v___jp_4947_:
{
if (lean_obj_tag(v___y_4948_) == 0)
{
lean_object* v_a_4949_; 
v_a_4949_ = lean_ctor_get(v___y_4948_, 0);
lean_inc(v_a_4949_);
lean_dec_ref_known(v___y_4948_, 1);
v_a_4931_ = v_a_4949_;
goto v___jp_4930_;
}
else
{
lean_object* v_a_4950_; 
v_a_4950_ = lean_ctor_get(v___y_4948_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___y_4948_, 1);
v_a_4927_ = v_a_4950_;
goto v___jp_4926_;
}
}
v_reusejp_4951_:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; uint8_t v_transparency_4955_; uint8_t v___x_4956_; 
v___x_4953_ = lean_st_ref_put(v___y_4867_, v___x_4952_);
v___x_4954_ = l_Lean_Meta_Context_config(v___x_4916_);
v_transparency_4955_ = lean_ctor_get_uint8(v___x_4954_, 9);
lean_dec_ref(v___x_4954_);
v___x_4956_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4955_, v___x_4874_);
if (v___x_4956_ == 0)
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; uint8_t v_transparency_4960_; uint8_t v___x_4961_; uint8_t v___x_4962_; 
lean_dec_ref_known(v___x_4916_, 7);
lean_inc_ref(v_keyedConfig_4906_);
v___x_4957_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4874_, v_keyedConfig_4906_);
lean_inc(v_customCanUnfoldPredicate_x3f_4912_);
lean_inc(v_synthPendingDepth_4911_);
lean_inc(v_defEqCtx_x3f_4910_);
lean_inc_ref(v_localInstances_4909_);
lean_inc_ref(v_lctx_4908_);
lean_inc(v_zetaDeltaSet_4907_);
lean_inc_ref(v___x_4957_);
v___x_4958_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
lean_ctor_set(v___x_4958_, 1, v_zetaDeltaSet_4907_);
lean_ctor_set(v___x_4958_, 2, v_lctx_4908_);
lean_ctor_set(v___x_4958_, 3, v_localInstances_4909_);
lean_ctor_set(v___x_4958_, 4, v_defEqCtx_x3f_4910_);
lean_ctor_set(v___x_4958_, 5, v_synthPendingDepth_4911_);
lean_ctor_set(v___x_4958_, 6, v_customCanUnfoldPredicate_x3f_4912_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7, v___x_4863_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7 + 1, v_univApprox_4913_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4914_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7 + 3, v_cacheInferType_4915_);
v___x_4959_ = l_Lean_Meta_Context_config(v___x_4958_);
v_transparency_4960_ = lean_ctor_get_uint8(v___x_4959_, 9);
lean_dec_ref(v___x_4959_);
v___x_4961_ = 1;
v___x_4962_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4960_, v___x_4961_);
if (v___x_4962_ == 0)
{
lean_object* v___x_4963_; 
lean_dec_ref(v___x_4957_);
lean_inc(v___y_4869_);
lean_inc_ref(v___y_4868_);
lean_inc(v___y_4867_);
v___x_4963_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4863_, v___f_4878_, v___x_4958_, v___y_4867_, v___y_4868_, v___y_4869_);
v___y_4944_ = v___x_4963_;
goto v___jp_4943_;
}
else
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
lean_dec_ref_known(v___x_4958_, 7);
v___x_4964_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4961_, v___x_4957_);
lean_inc(v_customCanUnfoldPredicate_x3f_4912_);
lean_inc(v_synthPendingDepth_4911_);
lean_inc(v_defEqCtx_x3f_4910_);
lean_inc_ref(v_localInstances_4909_);
lean_inc_ref(v_lctx_4908_);
lean_inc(v_zetaDeltaSet_4907_);
v___x_4965_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4965_, 0, v___x_4964_);
lean_ctor_set(v___x_4965_, 1, v_zetaDeltaSet_4907_);
lean_ctor_set(v___x_4965_, 2, v_lctx_4908_);
lean_ctor_set(v___x_4965_, 3, v_localInstances_4909_);
lean_ctor_set(v___x_4965_, 4, v_defEqCtx_x3f_4910_);
lean_ctor_set(v___x_4965_, 5, v_synthPendingDepth_4911_);
lean_ctor_set(v___x_4965_, 6, v_customCanUnfoldPredicate_x3f_4912_);
lean_ctor_set_uint8(v___x_4965_, sizeof(void*)*7, v___x_4863_);
lean_ctor_set_uint8(v___x_4965_, sizeof(void*)*7 + 1, v_univApprox_4913_);
lean_ctor_set_uint8(v___x_4965_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4914_);
lean_ctor_set_uint8(v___x_4965_, sizeof(void*)*7 + 3, v_cacheInferType_4915_);
lean_inc(v___y_4869_);
lean_inc_ref(v___y_4868_);
lean_inc(v___y_4867_);
v___x_4966_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4863_, v___f_4878_, v___x_4965_, v___y_4867_, v___y_4868_, v___y_4869_);
v___y_4944_ = v___x_4966_;
goto v___jp_4943_;
}
}
else
{
uint8_t v___x_4967_; uint8_t v___x_4968_; 
v___x_4967_ = 1;
v___x_4968_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4955_, v___x_4967_);
if (v___x_4968_ == 0)
{
lean_object* v___x_4969_; 
lean_inc(v___y_4869_);
lean_inc_ref(v___y_4868_);
lean_inc(v___y_4867_);
v___x_4969_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4956_, v___f_4878_, v___x_4916_, v___y_4867_, v___y_4868_, v___y_4869_);
v___y_4948_ = v___x_4969_;
goto v___jp_4947_;
}
else
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
lean_dec_ref_known(v___x_4916_, 7);
lean_inc_ref(v_keyedConfig_4906_);
v___x_4970_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4967_, v_keyedConfig_4906_);
lean_inc(v_customCanUnfoldPredicate_x3f_4912_);
lean_inc(v_synthPendingDepth_4911_);
lean_inc(v_defEqCtx_x3f_4910_);
lean_inc_ref(v_localInstances_4909_);
lean_inc_ref(v_lctx_4908_);
lean_inc(v_zetaDeltaSet_4907_);
v___x_4971_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4971_, 0, v___x_4970_);
lean_ctor_set(v___x_4971_, 1, v_zetaDeltaSet_4907_);
lean_ctor_set(v___x_4971_, 2, v_lctx_4908_);
lean_ctor_set(v___x_4971_, 3, v_localInstances_4909_);
lean_ctor_set(v___x_4971_, 4, v_defEqCtx_x3f_4910_);
lean_ctor_set(v___x_4971_, 5, v_synthPendingDepth_4911_);
lean_ctor_set(v___x_4971_, 6, v_customCanUnfoldPredicate_x3f_4912_);
lean_ctor_set_uint8(v___x_4971_, sizeof(void*)*7, v___x_4863_);
lean_ctor_set_uint8(v___x_4971_, sizeof(void*)*7 + 1, v_univApprox_4913_);
lean_ctor_set_uint8(v___x_4971_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4914_);
lean_ctor_set_uint8(v___x_4971_, sizeof(void*)*7 + 3, v_cacheInferType_4915_);
lean_inc(v___y_4869_);
lean_inc_ref(v___y_4868_);
lean_inc(v___y_4867_);
v___x_4972_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4956_, v___f_4878_, v___x_4971_, v___y_4867_, v___y_4868_, v___y_4869_);
v___y_4948_ = v___x_4972_;
goto v___jp_4947_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_4978_, lean_object* v_e_4979_, lean_object* v_cls_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
uint8_t v___x_14349__boxed_4986_; lean_object* v_res_4987_; 
v___x_14349__boxed_4986_ = lean_unbox(v___x_4978_);
v_res_4987_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14349__boxed_4986_, v_e_4979_, v_cls_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
if (lean_obj_tag(v_x_4988_) == 0)
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5002_; 
v_a_4994_ = lean_ctor_get(v_x_4988_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_x_4988_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4996_ = v_x_4988_;
v_isShared_4997_ = v_isSharedCheck_5002_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v_x_4988_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5002_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4998_; lean_object* v___x_5000_; 
v___x_4998_ = l_Lean_Exception_toMessageData(v_a_4994_);
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v___x_4998_);
v___x_5000_ = v___x_4996_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5011_; 
v_a_5003_ = lean_ctor_get(v_x_4988_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v_x_4988_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5005_ = v_x_4988_;
v_isShared_5006_ = v_isSharedCheck_5011_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v_x_4988_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5011_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v_snd_5007_; lean_object* v___x_5009_; 
v_snd_5007_ = lean_ctor_get(v_a_5003_, 1);
lean_inc(v_snd_5007_);
lean_dec(v_a_5003_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set_tag(v___x_5005_, 0);
lean_ctor_set(v___x_5005_, 0, v_snd_5007_);
v___x_5009_ = v___x_5005_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_snd_5007_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(lean_object* v_oldTraces_5019_, lean_object* v_data_5020_, lean_object* v_ref_5021_, lean_object* v_msg_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v_toCold_5028_; lean_object* v_currRecDepth_5029_; lean_object* v_ref_5030_; uint16_t v_optionFlags_5031_; uint8_t v_suppressElabErrors_5032_; uint8_t v_checkDeprecated_5033_; uint8_t v_isRecordingDeps_5034_; lean_object* v_ref_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v_traceState_5038_; lean_object* v_traces_5039_; lean_object* v___x_5040_; size_t v_sz_5041_; size_t v___x_5042_; lean_object* v___x_5043_; lean_object* v_msg_5044_; lean_object* v___x_5045_; lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5084_; 
v_toCold_5028_ = lean_ctor_get(v___y_5025_, 0);
v_currRecDepth_5029_ = lean_ctor_get(v___y_5025_, 1);
v_ref_5030_ = lean_ctor_get(v___y_5025_, 2);
v_optionFlags_5031_ = lean_ctor_get_uint16(v___y_5025_, sizeof(void*)*3);
v_suppressElabErrors_5032_ = lean_ctor_get_uint8(v___y_5025_, sizeof(void*)*3 + 2);
v_checkDeprecated_5033_ = lean_ctor_get_uint8(v___y_5025_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5034_ = lean_ctor_get_uint8(v___y_5025_, sizeof(void*)*3 + 4);
v_ref_5035_ = l_Lean_replaceRef(v_ref_5021_, v_ref_5030_);
lean_inc(v_currRecDepth_5029_);
lean_inc_ref(v_toCold_5028_);
v___x_5036_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5036_, 0, v_toCold_5028_);
lean_ctor_set(v___x_5036_, 1, v_currRecDepth_5029_);
lean_ctor_set(v___x_5036_, 2, v_ref_5035_);
lean_ctor_set_uint16(v___x_5036_, sizeof(void*)*3, v_optionFlags_5031_);
lean_ctor_set_uint8(v___x_5036_, sizeof(void*)*3 + 2, v_suppressElabErrors_5032_);
lean_ctor_set_uint8(v___x_5036_, sizeof(void*)*3 + 3, v_checkDeprecated_5033_);
lean_ctor_set_uint8(v___x_5036_, sizeof(void*)*3 + 4, v_isRecordingDeps_5034_);
v___x_5037_ = lean_st_ref_get(v___y_5026_);
v_traceState_5038_ = lean_ctor_get(v___x_5037_, 4);
lean_inc_ref(v_traceState_5038_);
lean_dec(v___x_5037_);
v_traces_5039_ = lean_ctor_get(v_traceState_5038_, 0);
lean_inc_ref(v_traces_5039_);
lean_dec_ref(v_traceState_5038_);
v___x_5040_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5039_);
lean_dec_ref(v_traces_5039_);
v_sz_5041_ = lean_array_size(v___x_5040_);
v___x_5042_ = ((size_t)0ULL);
v___x_5043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5041_, v___x_5042_, v___x_5040_);
v_msg_5044_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5044_, 0, v_data_5020_);
lean_ctor_set(v_msg_5044_, 1, v_msg_5022_);
lean_ctor_set(v_msg_5044_, 2, v___x_5043_);
v___x_5045_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5044_, v___y_5023_, v___y_5024_, v___x_5036_, v___y_5026_);
lean_dec_ref_known(v___x_5036_, 3);
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5048_ = v___x_5045_;
v_isShared_5049_ = v_isSharedCheck_5084_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5045_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5084_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5050_; lean_object* v_traceState_5051_; lean_object* v_env_5052_; lean_object* v_nextMacroScope_5053_; lean_object* v_ngen_5054_; lean_object* v_auxDeclNGen_5055_; lean_object* v_cache_5056_; lean_object* v_recordedDeps_5057_; lean_object* v_messages_5058_; lean_object* v_infoState_5059_; lean_object* v_snapshotTasks_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5083_; 
v___x_5050_ = lean_st_ref_take(v___y_5026_);
v_traceState_5051_ = lean_ctor_get(v___x_5050_, 4);
v_env_5052_ = lean_ctor_get(v___x_5050_, 0);
v_nextMacroScope_5053_ = lean_ctor_get(v___x_5050_, 1);
v_ngen_5054_ = lean_ctor_get(v___x_5050_, 2);
v_auxDeclNGen_5055_ = lean_ctor_get(v___x_5050_, 3);
v_cache_5056_ = lean_ctor_get(v___x_5050_, 5);
v_recordedDeps_5057_ = lean_ctor_get(v___x_5050_, 6);
v_messages_5058_ = lean_ctor_get(v___x_5050_, 7);
v_infoState_5059_ = lean_ctor_get(v___x_5050_, 8);
v_snapshotTasks_5060_ = lean_ctor_get(v___x_5050_, 9);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5062_ = v___x_5050_;
v_isShared_5063_ = v_isSharedCheck_5083_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_snapshotTasks_5060_);
lean_inc(v_infoState_5059_);
lean_inc(v_messages_5058_);
lean_inc(v_recordedDeps_5057_);
lean_inc(v_cache_5056_);
lean_inc(v_traceState_5051_);
lean_inc(v_auxDeclNGen_5055_);
lean_inc(v_ngen_5054_);
lean_inc(v_nextMacroScope_5053_);
lean_inc(v_env_5052_);
lean_dec(v___x_5050_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5083_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
uint64_t v_tid_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5081_; 
v_tid_5064_ = lean_ctor_get_uint64(v_traceState_5051_, sizeof(void*)*1);
v_isSharedCheck_5081_ = !lean_is_exclusive(v_traceState_5051_);
if (v_isSharedCheck_5081_ == 0)
{
lean_object* v_unused_5082_; 
v_unused_5082_ = lean_ctor_get(v_traceState_5051_, 0);
lean_dec(v_unused_5082_);
v___x_5066_ = v_traceState_5051_;
v_isShared_5067_ = v_isSharedCheck_5081_;
goto v_resetjp_5065_;
}
else
{
lean_dec(v_traceState_5051_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5081_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5072_; 
v___x_5068_ = lean_box(0);
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v_ref_5021_);
lean_ctor_set(v___x_5069_, 1, v_a_5046_);
v___x_5070_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5019_, v___x_5069_);
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 0, v___x_5070_);
v___x_5072_ = v___x_5066_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5070_);
lean_ctor_set_uint64(v_reuseFailAlloc_5080_, sizeof(void*)*1, v_tid_5064_);
v___x_5072_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
lean_object* v___x_5074_; 
if (v_isShared_5063_ == 0)
{
lean_ctor_set(v___x_5062_, 4, v___x_5072_);
v___x_5074_ = v___x_5062_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_env_5052_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v_nextMacroScope_5053_);
lean_ctor_set(v_reuseFailAlloc_5079_, 2, v_ngen_5054_);
lean_ctor_set(v_reuseFailAlloc_5079_, 3, v_auxDeclNGen_5055_);
lean_ctor_set(v_reuseFailAlloc_5079_, 4, v___x_5072_);
lean_ctor_set(v_reuseFailAlloc_5079_, 5, v_cache_5056_);
lean_ctor_set(v_reuseFailAlloc_5079_, 6, v_recordedDeps_5057_);
lean_ctor_set(v_reuseFailAlloc_5079_, 7, v_messages_5058_);
lean_ctor_set(v_reuseFailAlloc_5079_, 8, v_infoState_5059_);
lean_ctor_set(v_reuseFailAlloc_5079_, 9, v_snapshotTasks_5060_);
v___x_5074_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5077_; 
v___x_5075_ = lean_st_ref_put(v___y_5026_, v___x_5074_);
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 0, v___x_5068_);
v___x_5077_ = v___x_5048_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v___x_5068_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4___boxed(lean_object* v_oldTraces_5085_, lean_object* v_data_5086_, lean_object* v_ref_5087_, lean_object* v_msg_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(v_oldTraces_5085_, v_data_5086_, v_ref_5087_, v_msg_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
lean_dec(v___y_5090_);
lean_dec_ref(v___y_5089_);
return v_res_5094_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6(lean_object* v_e_5095_){
_start:
{
if (lean_obj_tag(v_e_5095_) == 0)
{
uint8_t v___x_5096_; 
v___x_5096_ = 2;
return v___x_5096_;
}
else
{
uint8_t v___x_5097_; 
v___x_5097_ = 0;
return v___x_5097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6___boxed(lean_object* v_e_5098_){
_start:
{
uint8_t v_res_5099_; lean_object* v_r_5100_; 
v_res_5099_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6(v_e_5098_);
lean_dec_ref(v_e_5098_);
v_r_5100_ = lean_box(v_res_5099_);
return v_r_5100_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(lean_object* v_x_5101_){
_start:
{
if (lean_obj_tag(v_x_5101_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
v_a_5103_ = lean_ctor_get(v_x_5101_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v_x_5101_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v_x_5101_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v_x_5101_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
lean_ctor_set_tag(v___x_5105_, 1);
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
v_a_5111_ = lean_ctor_get(v_x_5101_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v_x_5101_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v_x_5101_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v_x_5101_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
lean_ctor_set_tag(v___x_5113_, 0);
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg___boxed(lean_object* v_x_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_x_5119_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(lean_object* v_cls_5122_, uint8_t v_collapsed_5123_, lean_object* v_tag_5124_, lean_object* v_opts_5125_, uint8_t v_clsEnabled_5126_, lean_object* v_oldTraces_5127_, lean_object* v_msg_5128_, lean_object* v_resStartStop_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_fst_5135_; lean_object* v_snd_5136_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v_data_5140_; lean_object* v_fst_5151_; lean_object* v_snd_5152_; lean_object* v___x_5153_; uint8_t v___x_5154_; lean_object* v___y_5156_; lean_object* v_a_5157_; uint8_t v___y_5172_; double v___y_5204_; 
v_fst_5135_ = lean_ctor_get(v_resStartStop_5129_, 0);
lean_inc(v_fst_5135_);
v_snd_5136_ = lean_ctor_get(v_resStartStop_5129_, 1);
lean_inc(v_snd_5136_);
lean_dec_ref(v_resStartStop_5129_);
v_fst_5151_ = lean_ctor_get(v_snd_5136_, 0);
lean_inc(v_fst_5151_);
v_snd_5152_ = lean_ctor_get(v_snd_5136_, 1);
lean_inc(v_snd_5152_);
lean_dec(v_snd_5136_);
v___x_5153_ = l_Lean_trace_profiler;
v___x_5154_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5125_, v___x_5153_);
if (v___x_5154_ == 0)
{
v___y_5172_ = v___x_5154_;
goto v___jp_5171_;
}
else
{
lean_object* v___x_5209_; uint8_t v___x_5210_; 
v___x_5209_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5210_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5125_, v___x_5209_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; lean_object* v___x_5212_; double v___x_5213_; double v___x_5214_; double v___x_5215_; 
v___x_5211_ = l_Lean_trace_profiler_threshold;
v___x_5212_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5125_, v___x_5211_);
v___x_5213_ = lean_float_of_nat(v___x_5212_);
v___x_5214_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5215_ = lean_float_div(v___x_5213_, v___x_5214_);
v___y_5204_ = v___x_5215_;
goto v___jp_5203_;
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5217_; double v___x_5218_; 
v___x_5216_ = l_Lean_trace_profiler_threshold;
v___x_5217_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5125_, v___x_5216_);
v___x_5218_ = lean_float_of_nat(v___x_5217_);
v___y_5204_ = v___x_5218_;
goto v___jp_5203_;
}
}
v___jp_5137_:
{
lean_object* v___x_5141_; 
lean_inc(v___y_5138_);
v___x_5141_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(v_oldTraces_5127_, v_data_5140_, v___y_5138_, v___y_5139_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v___x_5142_; 
lean_dec_ref_known(v___x_5141_, 1);
v___x_5142_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_fst_5135_);
return v___x_5142_;
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec(v_fst_5135_);
v_a_5143_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5141_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5141_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
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
v___jp_5155_:
{
uint8_t v_result_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; double v___x_5161_; lean_object* v_data_5162_; 
v_result_5158_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6(v_fst_5135_);
v___x_5159_ = lean_box(v_result_5158_);
v___x_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5160_, 0, v___x_5159_);
v___x_5161_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5124_);
lean_inc_ref(v___x_5160_);
lean_inc(v_cls_5122_);
v_data_5162_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5162_, 0, v_cls_5122_);
lean_ctor_set(v_data_5162_, 1, v___x_5160_);
lean_ctor_set(v_data_5162_, 2, v_tag_5124_);
lean_ctor_set_float(v_data_5162_, sizeof(void*)*3, v___x_5161_);
lean_ctor_set_float(v_data_5162_, sizeof(void*)*3 + 8, v___x_5161_);
lean_ctor_set_uint8(v_data_5162_, sizeof(void*)*3 + 16, v_collapsed_5123_);
if (v___x_5154_ == 0)
{
lean_dec_ref_known(v___x_5160_, 1);
lean_dec(v_snd_5152_);
lean_dec(v_fst_5151_);
lean_dec_ref(v_tag_5124_);
lean_dec(v_cls_5122_);
v___y_5138_ = v___y_5156_;
v___y_5139_ = v_a_5157_;
v_data_5140_ = v_data_5162_;
goto v___jp_5137_;
}
else
{
lean_object* v_data_5163_; double v___x_5164_; double v___x_5165_; 
lean_dec_ref_known(v_data_5162_, 3);
v_data_5163_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5163_, 0, v_cls_5122_);
lean_ctor_set(v_data_5163_, 1, v___x_5160_);
lean_ctor_set(v_data_5163_, 2, v_tag_5124_);
v___x_5164_ = lean_unbox_float(v_fst_5151_);
lean_dec(v_fst_5151_);
lean_ctor_set_float(v_data_5163_, sizeof(void*)*3, v___x_5164_);
v___x_5165_ = lean_unbox_float(v_snd_5152_);
lean_dec(v_snd_5152_);
lean_ctor_set_float(v_data_5163_, sizeof(void*)*3 + 8, v___x_5165_);
lean_ctor_set_uint8(v_data_5163_, sizeof(void*)*3 + 16, v_collapsed_5123_);
v___y_5138_ = v___y_5156_;
v___y_5139_ = v_a_5157_;
v_data_5140_ = v_data_5163_;
goto v___jp_5137_;
}
}
v___jp_5166_:
{
lean_object* v_ref_5167_; lean_object* v___x_5168_; 
v_ref_5167_ = lean_ctor_get(v___y_5132_, 2);
lean_inc(v___y_5133_);
lean_inc_ref(v___y_5132_);
lean_inc(v___y_5131_);
lean_inc_ref(v___y_5130_);
lean_inc(v_fst_5135_);
v___x_5168_ = lean_apply_6(v_msg_5128_, v_fst_5135_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, lean_box(0));
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5168_, 1);
v___y_5156_ = v_ref_5167_;
v_a_5157_ = v_a_5169_;
goto v___jp_5155_;
}
else
{
lean_object* v___x_5170_; 
lean_dec_ref_known(v___x_5168_, 1);
v___x_5170_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5156_ = v_ref_5167_;
v_a_5157_ = v___x_5170_;
goto v___jp_5155_;
}
}
v___jp_5171_:
{
if (v_clsEnabled_5126_ == 0)
{
if (v___y_5172_ == 0)
{
lean_object* v___x_5173_; lean_object* v_traceState_5174_; lean_object* v_env_5175_; lean_object* v_nextMacroScope_5176_; lean_object* v_ngen_5177_; lean_object* v_auxDeclNGen_5178_; lean_object* v_cache_5179_; lean_object* v_recordedDeps_5180_; lean_object* v_messages_5181_; lean_object* v_infoState_5182_; lean_object* v_snapshotTasks_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5202_; 
lean_dec(v_snd_5152_);
lean_dec(v_fst_5151_);
lean_dec_ref(v_msg_5128_);
lean_dec_ref(v_tag_5124_);
lean_dec(v_cls_5122_);
v___x_5173_ = lean_st_ref_take(v___y_5133_);
v_traceState_5174_ = lean_ctor_get(v___x_5173_, 4);
v_env_5175_ = lean_ctor_get(v___x_5173_, 0);
v_nextMacroScope_5176_ = lean_ctor_get(v___x_5173_, 1);
v_ngen_5177_ = lean_ctor_get(v___x_5173_, 2);
v_auxDeclNGen_5178_ = lean_ctor_get(v___x_5173_, 3);
v_cache_5179_ = lean_ctor_get(v___x_5173_, 5);
v_recordedDeps_5180_ = lean_ctor_get(v___x_5173_, 6);
v_messages_5181_ = lean_ctor_get(v___x_5173_, 7);
v_infoState_5182_ = lean_ctor_get(v___x_5173_, 8);
v_snapshotTasks_5183_ = lean_ctor_get(v___x_5173_, 9);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5185_ = v___x_5173_;
v_isShared_5186_ = v_isSharedCheck_5202_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_snapshotTasks_5183_);
lean_inc(v_infoState_5182_);
lean_inc(v_messages_5181_);
lean_inc(v_recordedDeps_5180_);
lean_inc(v_cache_5179_);
lean_inc(v_traceState_5174_);
lean_inc(v_auxDeclNGen_5178_);
lean_inc(v_ngen_5177_);
lean_inc(v_nextMacroScope_5176_);
lean_inc(v_env_5175_);
lean_dec(v___x_5173_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5202_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
uint64_t v_tid_5187_; lean_object* v_traces_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5201_; 
v_tid_5187_ = lean_ctor_get_uint64(v_traceState_5174_, sizeof(void*)*1);
v_traces_5188_ = lean_ctor_get(v_traceState_5174_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v_traceState_5174_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5190_ = v_traceState_5174_;
v_isShared_5191_ = v_isSharedCheck_5201_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_traces_5188_);
lean_dec(v_traceState_5174_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5201_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5192_; lean_object* v___x_5194_; 
v___x_5192_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5127_, v_traces_5188_);
lean_dec_ref(v_traces_5188_);
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 0, v___x_5192_);
v___x_5194_ = v___x_5190_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___x_5192_);
lean_ctor_set_uint64(v_reuseFailAlloc_5200_, sizeof(void*)*1, v_tid_5187_);
v___x_5194_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
lean_object* v___x_5196_; 
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 4, v___x_5194_);
v___x_5196_ = v___x_5185_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_env_5175_);
lean_ctor_set(v_reuseFailAlloc_5199_, 1, v_nextMacroScope_5176_);
lean_ctor_set(v_reuseFailAlloc_5199_, 2, v_ngen_5177_);
lean_ctor_set(v_reuseFailAlloc_5199_, 3, v_auxDeclNGen_5178_);
lean_ctor_set(v_reuseFailAlloc_5199_, 4, v___x_5194_);
lean_ctor_set(v_reuseFailAlloc_5199_, 5, v_cache_5179_);
lean_ctor_set(v_reuseFailAlloc_5199_, 6, v_recordedDeps_5180_);
lean_ctor_set(v_reuseFailAlloc_5199_, 7, v_messages_5181_);
lean_ctor_set(v_reuseFailAlloc_5199_, 8, v_infoState_5182_);
lean_ctor_set(v_reuseFailAlloc_5199_, 9, v_snapshotTasks_5183_);
v___x_5196_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5197_ = lean_st_ref_put(v___y_5133_, v___x_5196_);
v___x_5198_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_fst_5135_);
return v___x_5198_;
}
}
}
}
}
else
{
goto v___jp_5166_;
}
}
else
{
goto v___jp_5166_;
}
}
v___jp_5203_:
{
double v___x_5205_; double v___x_5206_; double v___x_5207_; uint8_t v___x_5208_; 
v___x_5205_ = lean_unbox_float(v_snd_5152_);
v___x_5206_ = lean_unbox_float(v_fst_5151_);
v___x_5207_ = lean_float_sub(v___x_5205_, v___x_5206_);
v___x_5208_ = lean_float_decLt(v___y_5204_, v___x_5207_);
v___y_5172_ = v___x_5208_;
goto v___jp_5171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3___boxed(lean_object* v_cls_5219_, lean_object* v_collapsed_5220_, lean_object* v_tag_5221_, lean_object* v_opts_5222_, lean_object* v_clsEnabled_5223_, lean_object* v_oldTraces_5224_, lean_object* v_msg_5225_, lean_object* v_resStartStop_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
uint8_t v_collapsed_boxed_5232_; uint8_t v_clsEnabled_boxed_5233_; lean_object* v_res_5234_; 
v_collapsed_boxed_5232_ = lean_unbox(v_collapsed_5220_);
v_clsEnabled_boxed_5233_ = lean_unbox(v_clsEnabled_5223_);
v_res_5234_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5219_, v_collapsed_boxed_5232_, v_tag_5221_, v_opts_5222_, v_clsEnabled_boxed_5233_, v_oldTraces_5224_, v_msg_5225_, v_resStartStop_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
lean_dec_ref(v_opts_5222_);
return v_res_5234_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; 
v_cls_5239_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5240_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5241_ = l_Lean_Name_append(v___x_5240_, v_cls_5239_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_){
_start:
{
lean_object* v___y_5249_; lean_object* v_toCold_5267_; lean_object* v_options_5268_; lean_object* v_inheritedTraceOptions_5269_; uint8_t v_hasTrace_5270_; lean_object* v_cls_5271_; uint8_t v___x_5272_; 
v_toCold_5267_ = lean_ctor_get(v_a_5245_, 0);
v_options_5268_ = lean_ctor_get(v_toCold_5267_, 2);
v_inheritedTraceOptions_5269_ = lean_ctor_get(v_toCold_5267_, 11);
v_hasTrace_5270_ = lean_ctor_get_uint8(v_options_5268_, sizeof(void*)*1);
v_cls_5271_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5272_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5242_);
if (v_hasTrace_5270_ == 0)
{
lean_object* v___x_5273_; 
v___x_5273_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5272_, v_e_5242_, v_cls_5271_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
v___y_5249_ = v___x_5273_;
goto v___jp_5248_;
}
else
{
lean_object* v___f_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; uint8_t v___x_5277_; lean_object* v___y_5279_; lean_object* v___y_5280_; lean_object* v_a_5281_; lean_object* v___y_5294_; lean_object* v___y_5295_; lean_object* v_a_5296_; 
v___f_5274_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5275_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5276_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5277_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5269_, v_options_5268_, v___x_5276_);
if (v___x_5277_ == 0)
{
lean_object* v___x_5346_; uint8_t v___x_5347_; 
v___x_5346_ = l_Lean_trace_profiler;
v___x_5347_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5268_, v___x_5346_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; 
v___x_5348_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5272_, v_e_5242_, v_cls_5271_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
v___y_5249_ = v___x_5348_;
goto v___jp_5248_;
}
else
{
goto v___jp_5305_;
}
}
else
{
goto v___jp_5305_;
}
v___jp_5278_:
{
lean_object* v___x_5282_; double v___x_5283_; double v___x_5284_; double v___x_5285_; double v___x_5286_; double v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5282_ = lean_io_mono_nanos_now();
v___x_5283_ = lean_float_of_nat(v___y_5279_);
v___x_5284_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5285_ = lean_float_div(v___x_5283_, v___x_5284_);
v___x_5286_ = lean_float_of_nat(v___x_5282_);
v___x_5287_ = lean_float_div(v___x_5286_, v___x_5284_);
v___x_5288_ = lean_box_float(v___x_5285_);
v___x_5289_ = lean_box_float(v___x_5287_);
v___x_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5288_);
lean_ctor_set(v___x_5290_, 1, v___x_5289_);
v___x_5291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5291_, 0, v_a_5281_);
lean_ctor_set(v___x_5291_, 1, v___x_5290_);
v___x_5292_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5271_, v_hasTrace_5270_, v___x_5275_, v_options_5268_, v___x_5277_, v___y_5280_, v___f_5274_, v___x_5291_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
v___y_5249_ = v___x_5292_;
goto v___jp_5248_;
}
v___jp_5293_:
{
lean_object* v___x_5297_; double v___x_5298_; double v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5297_ = lean_io_get_num_heartbeats();
v___x_5298_ = lean_float_of_nat(v___y_5294_);
v___x_5299_ = lean_float_of_nat(v___x_5297_);
v___x_5300_ = lean_box_float(v___x_5298_);
v___x_5301_ = lean_box_float(v___x_5299_);
v___x_5302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5302_, 0, v___x_5300_);
lean_ctor_set(v___x_5302_, 1, v___x_5301_);
v___x_5303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5303_, 0, v_a_5296_);
lean_ctor_set(v___x_5303_, 1, v___x_5302_);
v___x_5304_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5271_, v_hasTrace_5270_, v___x_5275_, v_options_5268_, v___x_5277_, v___y_5295_, v___f_5274_, v___x_5303_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
v___y_5249_ = v___x_5304_;
goto v___jp_5248_;
}
v___jp_5305_:
{
lean_object* v___x_5306_; lean_object* v_a_5307_; lean_object* v___x_5308_; uint8_t v___x_5309_; 
v___x_5306_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v_a_5246_);
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
lean_dec_ref(v___x_5306_);
v___x_5308_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5309_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5268_, v___x_5308_);
if (v___x_5309_ == 0)
{
lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5310_ = lean_io_mono_nanos_now();
v___x_5311_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5272_, v_e_5242_, v_cls_5271_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5311_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5311_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
lean_ctor_set_tag(v___x_5314_, 1);
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
v___y_5279_ = v___x_5310_;
v___y_5280_ = v_a_5307_;
v_a_5281_ = v___x_5317_;
goto v___jp_5278_;
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
v_a_5320_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5311_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5311_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
lean_ctor_set_tag(v___x_5322_, 0);
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
v___y_5279_ = v___x_5310_;
v___y_5280_ = v_a_5307_;
v_a_5281_ = v___x_5325_;
goto v___jp_5278_;
}
}
}
}
else
{
lean_object* v___x_5328_; lean_object* v___x_5329_; 
v___x_5328_ = lean_io_get_num_heartbeats();
v___x_5329_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5272_, v_e_5242_, v_cls_5271_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5332_ = v___x_5329_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5329_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
lean_ctor_set_tag(v___x_5332_, 1);
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
v___y_5294_ = v___x_5328_;
v___y_5295_ = v_a_5307_;
v_a_5296_ = v___x_5335_;
goto v___jp_5293_;
}
}
}
else
{
lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
v_a_5338_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5340_ = v___x_5329_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_dec(v___x_5329_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
lean_ctor_set_tag(v___x_5340_, 0);
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5338_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
v___y_5294_ = v___x_5328_;
v___y_5295_ = v_a_5307_;
v_a_5296_ = v___x_5343_;
goto v___jp_5293_;
}
}
}
}
}
}
v___jp_5248_:
{
if (lean_obj_tag(v___y_5249_) == 0)
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5258_; 
v_a_5250_ = lean_ctor_get(v___y_5249_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___y_5249_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5252_ = v___y_5249_;
v_isShared_5253_ = v_isSharedCheck_5258_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___y_5249_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5258_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v_fst_5254_; lean_object* v___x_5256_; 
v_fst_5254_ = lean_ctor_get(v_a_5250_, 0);
lean_inc(v_fst_5254_);
lean_dec(v_a_5250_);
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 0, v_fst_5254_);
v___x_5256_ = v___x_5252_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_fst_5254_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
v_a_5259_ = lean_ctor_get(v___y_5249_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___y_5249_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___y_5249_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___y_5249_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_);
lean_dec(v_a_5353_);
lean_dec_ref(v_a_5352_);
lean_dec(v_a_5351_);
lean_dec_ref(v_a_5350_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1(lean_object* v_00_u03b2_5356_){
_start:
{
lean_object* v___x_5357_; 
v___x_5357_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(){
_start:
{
lean_object* v___x_5359_; 
v___x_5359_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___dummy_5360_){
_start:
{
lean_object* v_res_5361_; 
v_res_5361_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg();
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v_00_u03b2_5362_){
_start:
{
lean_object* v___x_5363_; 
v___x_5363_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
return v___x_5363_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5(lean_object* v_00_u03b1_5364_, lean_object* v_x_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v___x_5371_; 
v___x_5371_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_x_5365_);
return v___x_5371_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___boxed(lean_object* v_00_u03b1_5372_, lean_object* v_x_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5(v_00_u03b1_5372_, v_x_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5380_, lean_object* v___y_5381_){
_start:
{
uint8_t v___x_5383_; 
v___x_5383_ = l_Lean_Expr_hasMVar(v_e_5380_);
if (v___x_5383_ == 0)
{
lean_object* v___x_5384_; 
v___x_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5384_, 0, v_e_5380_);
return v___x_5384_;
}
else
{
lean_object* v___x_5385_; lean_object* v_mctx_5386_; lean_object* v___x_5387_; lean_object* v_fst_5388_; lean_object* v_snd_5389_; lean_object* v___x_5390_; lean_object* v_cache_5391_; lean_object* v_zetaDeltaFVarIds_5392_; lean_object* v_postponed_5393_; lean_object* v_diag_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5403_; 
v___x_5385_ = lean_st_ref_get(v___y_5381_);
v_mctx_5386_ = lean_ctor_get(v___x_5385_, 0);
lean_inc_ref(v_mctx_5386_);
lean_dec(v___x_5385_);
v___x_5387_ = l_Lean_instantiateMVarsCore(v_mctx_5386_, v_e_5380_);
v_fst_5388_ = lean_ctor_get(v___x_5387_, 0);
lean_inc(v_fst_5388_);
v_snd_5389_ = lean_ctor_get(v___x_5387_, 1);
lean_inc(v_snd_5389_);
lean_dec_ref(v___x_5387_);
v___x_5390_ = lean_st_ref_take(v___y_5381_);
v_cache_5391_ = lean_ctor_get(v___x_5390_, 1);
v_zetaDeltaFVarIds_5392_ = lean_ctor_get(v___x_5390_, 2);
v_postponed_5393_ = lean_ctor_get(v___x_5390_, 3);
v_diag_5394_ = lean_ctor_get(v___x_5390_, 4);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5403_ == 0)
{
lean_object* v_unused_5404_; 
v_unused_5404_ = lean_ctor_get(v___x_5390_, 0);
lean_dec(v_unused_5404_);
v___x_5396_ = v___x_5390_;
v_isShared_5397_ = v_isSharedCheck_5403_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_diag_5394_);
lean_inc(v_postponed_5393_);
lean_inc(v_zetaDeltaFVarIds_5392_);
lean_inc(v_cache_5391_);
lean_dec(v___x_5390_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5403_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 0, v_snd_5389_);
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_snd_5389_);
lean_ctor_set(v_reuseFailAlloc_5402_, 1, v_cache_5391_);
lean_ctor_set(v_reuseFailAlloc_5402_, 2, v_zetaDeltaFVarIds_5392_);
lean_ctor_set(v_reuseFailAlloc_5402_, 3, v_postponed_5393_);
lean_ctor_set(v_reuseFailAlloc_5402_, 4, v_diag_5394_);
v___x_5399_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5400_ = lean_st_ref_put(v___y_5381_, v___x_5399_);
v___x_5401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5401_, 0, v_fst_5388_);
return v___x_5401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5405_, v___y_5406_);
lean_dec(v___y_5406_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_){
_start:
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5409_, v___y_5411_);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5423_, lean_object* v_opts_5424_, lean_object* v_act_5425_, lean_object* v_decl_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v___x_5432_; lean_object* v___x_5433_; 
lean_inc(v___y_5430_);
lean_inc_ref(v___y_5429_);
lean_inc(v___y_5428_);
lean_inc_ref(v___y_5427_);
v___x_5432_ = lean_apply_4(v_act_5425_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
v___x_5433_ = l_Lean_profileitIOUnsafe___redArg(v_category_5423_, v_opts_5424_, v___x_5432_, v_decl_5426_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5434_, lean_object* v_opts_5435_, lean_object* v_act_5436_, lean_object* v_decl_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_){
_start:
{
lean_object* v_res_5443_; 
v_res_5443_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5434_, v_opts_5435_, v_act_5436_, v_decl_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec(v___y_5439_);
lean_dec_ref(v___y_5438_);
lean_dec_ref(v_opts_5435_);
lean_dec_ref(v_category_5434_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5444_, lean_object* v_category_5445_, lean_object* v_opts_5446_, lean_object* v_act_5447_, lean_object* v_decl_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
lean_object* v___x_5454_; 
v___x_5454_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5445_, v_opts_5446_, v_act_5447_, v_decl_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5455_, lean_object* v_category_5456_, lean_object* v_opts_5457_, lean_object* v_act_5458_, lean_object* v_decl_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5455_, v_category_5456_, v_opts_5457_, v_act_5458_, v_decl_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec_ref(v_opts_5457_);
lean_dec_ref(v_category_5456_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5466_, uint8_t v_isExporting_5467_, lean_object* v___x_5468_, lean_object* v___y_5469_, lean_object* v___x_5470_, lean_object* v_a_x3f_5471_){
_start:
{
lean_object* v___x_5473_; lean_object* v_env_5474_; lean_object* v_nextMacroScope_5475_; lean_object* v_ngen_5476_; lean_object* v_auxDeclNGen_5477_; lean_object* v_traceState_5478_; lean_object* v_recordedDeps_5479_; lean_object* v_messages_5480_; lean_object* v_infoState_5481_; lean_object* v_snapshotTasks_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5507_; 
v___x_5473_ = lean_st_ref_take(v___y_5466_);
v_env_5474_ = lean_ctor_get(v___x_5473_, 0);
v_nextMacroScope_5475_ = lean_ctor_get(v___x_5473_, 1);
v_ngen_5476_ = lean_ctor_get(v___x_5473_, 2);
v_auxDeclNGen_5477_ = lean_ctor_get(v___x_5473_, 3);
v_traceState_5478_ = lean_ctor_get(v___x_5473_, 4);
v_recordedDeps_5479_ = lean_ctor_get(v___x_5473_, 6);
v_messages_5480_ = lean_ctor_get(v___x_5473_, 7);
v_infoState_5481_ = lean_ctor_get(v___x_5473_, 8);
v_snapshotTasks_5482_ = lean_ctor_get(v___x_5473_, 9);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5507_ == 0)
{
lean_object* v_unused_5508_; 
v_unused_5508_ = lean_ctor_get(v___x_5473_, 5);
lean_dec(v_unused_5508_);
v___x_5484_ = v___x_5473_;
v_isShared_5485_ = v_isSharedCheck_5507_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_snapshotTasks_5482_);
lean_inc(v_infoState_5481_);
lean_inc(v_messages_5480_);
lean_inc(v_recordedDeps_5479_);
lean_inc(v_traceState_5478_);
lean_inc(v_auxDeclNGen_5477_);
lean_inc(v_ngen_5476_);
lean_inc(v_nextMacroScope_5475_);
lean_inc(v_env_5474_);
lean_dec(v___x_5473_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5507_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5486_; lean_object* v___x_5488_; 
v___x_5486_ = l_Lean_Environment_setExporting(v_env_5474_, v_isExporting_5467_);
if (v_isShared_5485_ == 0)
{
lean_ctor_set(v___x_5484_, 5, v___x_5468_);
lean_ctor_set(v___x_5484_, 0, v___x_5486_);
v___x_5488_ = v___x_5484_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5506_, 1, v_nextMacroScope_5475_);
lean_ctor_set(v_reuseFailAlloc_5506_, 2, v_ngen_5476_);
lean_ctor_set(v_reuseFailAlloc_5506_, 3, v_auxDeclNGen_5477_);
lean_ctor_set(v_reuseFailAlloc_5506_, 4, v_traceState_5478_);
lean_ctor_set(v_reuseFailAlloc_5506_, 5, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5506_, 6, v_recordedDeps_5479_);
lean_ctor_set(v_reuseFailAlloc_5506_, 7, v_messages_5480_);
lean_ctor_set(v_reuseFailAlloc_5506_, 8, v_infoState_5481_);
lean_ctor_set(v_reuseFailAlloc_5506_, 9, v_snapshotTasks_5482_);
v___x_5488_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v_mctx_5491_; lean_object* v_zetaDeltaFVarIds_5492_; lean_object* v_postponed_5493_; lean_object* v_diag_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5504_; 
v___x_5489_ = lean_st_ref_put(v___y_5466_, v___x_5488_);
v___x_5490_ = lean_st_ref_take(v___y_5469_);
v_mctx_5491_ = lean_ctor_get(v___x_5490_, 0);
v_zetaDeltaFVarIds_5492_ = lean_ctor_get(v___x_5490_, 2);
v_postponed_5493_ = lean_ctor_get(v___x_5490_, 3);
v_diag_5494_ = lean_ctor_get(v___x_5490_, 4);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5504_ == 0)
{
lean_object* v_unused_5505_; 
v_unused_5505_ = lean_ctor_get(v___x_5490_, 1);
lean_dec(v_unused_5505_);
v___x_5496_ = v___x_5490_;
v_isShared_5497_ = v_isSharedCheck_5504_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_diag_5494_);
lean_inc(v_postponed_5493_);
lean_inc(v_zetaDeltaFVarIds_5492_);
lean_inc(v_mctx_5491_);
lean_dec(v___x_5490_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5504_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5498_; lean_object* v___x_5500_; 
v___x_5498_ = lean_box(0);
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 1, v___x_5470_);
v___x_5500_ = v___x_5496_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_mctx_5491_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v___x_5470_);
lean_ctor_set(v_reuseFailAlloc_5503_, 2, v_zetaDeltaFVarIds_5492_);
lean_ctor_set(v_reuseFailAlloc_5503_, 3, v_postponed_5493_);
lean_ctor_set(v_reuseFailAlloc_5503_, 4, v_diag_5494_);
v___x_5500_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
lean_object* v___x_5501_; lean_object* v___x_5502_; 
v___x_5501_ = lean_st_ref_put(v___y_5469_, v___x_5500_);
v___x_5502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5502_, 0, v___x_5498_);
return v___x_5502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5509_, lean_object* v_isExporting_5510_, lean_object* v___x_5511_, lean_object* v___y_5512_, lean_object* v___x_5513_, lean_object* v_a_x3f_5514_, lean_object* v___y_5515_){
_start:
{
uint8_t v_isExporting_boxed_5516_; lean_object* v_res_5517_; 
v_isExporting_boxed_5516_ = lean_unbox(v_isExporting_5510_);
v_res_5517_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5509_, v_isExporting_boxed_5516_, v___x_5511_, v___y_5512_, v___x_5513_, v_a_x3f_5514_);
lean_dec(v_a_x3f_5514_);
lean_dec(v___y_5512_);
lean_dec(v___y_5509_);
return v_res_5517_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5518_; lean_object* v___x_5519_; 
v___x_5518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_5519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5518_);
return v___x_5519_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5520_; lean_object* v___x_5521_; 
v___x_5520_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5521_, 0, v___x_5520_);
lean_ctor_set(v___x_5521_, 1, v___x_5520_);
return v___x_5521_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; 
v___x_5522_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5523_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
v___x_5524_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
lean_ctor_set(v___x_5524_, 1, v___x_5522_);
lean_ctor_set(v___x_5524_, 2, v___x_5522_);
lean_ctor_set(v___x_5524_, 3, v___x_5522_);
lean_ctor_set(v___x_5524_, 4, v___x_5522_);
lean_ctor_set(v___x_5524_, 5, v___x_5522_);
lean_ctor_set(v___x_5524_, 6, v___x_5522_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5525_, uint8_t v_isExporting_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_){
_start:
{
lean_object* v___x_5532_; lean_object* v_env_5533_; lean_object* v___x_5534_; uint8_t v_isModule_5535_; 
v___x_5532_ = lean_st_ref_get(v___y_5530_);
v_env_5533_ = lean_ctor_get(v___x_5532_, 0);
lean_inc_ref(v_env_5533_);
lean_dec(v___x_5532_);
v___x_5534_ = l_Lean_Environment_header(v_env_5533_);
v_isModule_5535_ = lean_ctor_get_uint8(v___x_5534_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5534_);
if (v_isModule_5535_ == 0)
{
lean_object* v___x_5536_; 
lean_dec_ref(v_env_5533_);
lean_inc(v___y_5530_);
lean_inc_ref(v___y_5529_);
lean_inc(v___y_5528_);
lean_inc_ref(v___y_5527_);
v___x_5536_ = lean_apply_5(v_x_5525_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, lean_box(0));
return v___x_5536_;
}
else
{
uint8_t v_isExporting_5537_; 
v_isExporting_5537_ = lean_ctor_get_uint8(v_env_5533_, sizeof(void*)*13);
lean_dec_ref(v_env_5533_);
if (v_isExporting_5526_ == 0)
{
if (v_isExporting_5537_ == 0)
{
lean_object* v___x_5604_; 
lean_inc(v___y_5530_);
lean_inc_ref(v___y_5529_);
lean_inc(v___y_5528_);
lean_inc_ref(v___y_5527_);
v___x_5604_ = lean_apply_5(v_x_5525_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, lean_box(0));
return v___x_5604_;
}
else
{
goto v___jp_5538_;
}
}
else
{
if (v_isExporting_5537_ == 0)
{
goto v___jp_5538_;
}
else
{
lean_object* v___x_5605_; 
lean_inc(v___y_5530_);
lean_inc_ref(v___y_5529_);
lean_inc(v___y_5528_);
lean_inc_ref(v___y_5527_);
v___x_5605_ = lean_apply_5(v_x_5525_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, lean_box(0));
return v___x_5605_;
}
}
v___jp_5538_:
{
lean_object* v___x_5539_; lean_object* v_env_5540_; lean_object* v_nextMacroScope_5541_; lean_object* v_ngen_5542_; lean_object* v_auxDeclNGen_5543_; lean_object* v_traceState_5544_; lean_object* v_recordedDeps_5545_; lean_object* v_messages_5546_; lean_object* v_infoState_5547_; lean_object* v_snapshotTasks_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5602_; 
v___x_5539_ = lean_st_ref_take(v___y_5530_);
v_env_5540_ = lean_ctor_get(v___x_5539_, 0);
v_nextMacroScope_5541_ = lean_ctor_get(v___x_5539_, 1);
v_ngen_5542_ = lean_ctor_get(v___x_5539_, 2);
v_auxDeclNGen_5543_ = lean_ctor_get(v___x_5539_, 3);
v_traceState_5544_ = lean_ctor_get(v___x_5539_, 4);
v_recordedDeps_5545_ = lean_ctor_get(v___x_5539_, 6);
v_messages_5546_ = lean_ctor_get(v___x_5539_, 7);
v_infoState_5547_ = lean_ctor_get(v___x_5539_, 8);
v_snapshotTasks_5548_ = lean_ctor_get(v___x_5539_, 9);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5602_ == 0)
{
lean_object* v_unused_5603_; 
v_unused_5603_ = lean_ctor_get(v___x_5539_, 5);
lean_dec(v_unused_5603_);
v___x_5550_ = v___x_5539_;
v_isShared_5551_ = v_isSharedCheck_5602_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_snapshotTasks_5548_);
lean_inc(v_infoState_5547_);
lean_inc(v_messages_5546_);
lean_inc(v_recordedDeps_5545_);
lean_inc(v_traceState_5544_);
lean_inc(v_auxDeclNGen_5543_);
lean_inc(v_ngen_5542_);
lean_inc(v_nextMacroScope_5541_);
lean_inc(v_env_5540_);
lean_dec(v___x_5539_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5602_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5555_; 
v___x_5552_ = l_Lean_Environment_setExporting(v_env_5540_, v_isExporting_5526_);
v___x_5553_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 5, v___x_5553_);
lean_ctor_set(v___x_5550_, 0, v___x_5552_);
v___x_5555_ = v___x_5550_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v_nextMacroScope_5541_);
lean_ctor_set(v_reuseFailAlloc_5601_, 2, v_ngen_5542_);
lean_ctor_set(v_reuseFailAlloc_5601_, 3, v_auxDeclNGen_5543_);
lean_ctor_set(v_reuseFailAlloc_5601_, 4, v_traceState_5544_);
lean_ctor_set(v_reuseFailAlloc_5601_, 5, v___x_5553_);
lean_ctor_set(v_reuseFailAlloc_5601_, 6, v_recordedDeps_5545_);
lean_ctor_set(v_reuseFailAlloc_5601_, 7, v_messages_5546_);
lean_ctor_set(v_reuseFailAlloc_5601_, 8, v_infoState_5547_);
lean_ctor_set(v_reuseFailAlloc_5601_, 9, v_snapshotTasks_5548_);
v___x_5555_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v_mctx_5558_; lean_object* v_zetaDeltaFVarIds_5559_; lean_object* v_postponed_5560_; lean_object* v_diag_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5599_; 
v___x_5556_ = lean_st_ref_put(v___y_5530_, v___x_5555_);
v___x_5557_ = lean_st_ref_take(v___y_5528_);
v_mctx_5558_ = lean_ctor_get(v___x_5557_, 0);
v_zetaDeltaFVarIds_5559_ = lean_ctor_get(v___x_5557_, 2);
v_postponed_5560_ = lean_ctor_get(v___x_5557_, 3);
v_diag_5561_ = lean_ctor_get(v___x_5557_, 4);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5557_);
if (v_isSharedCheck_5599_ == 0)
{
lean_object* v_unused_5600_; 
v_unused_5600_ = lean_ctor_get(v___x_5557_, 1);
lean_dec(v_unused_5600_);
v___x_5563_ = v___x_5557_;
v_isShared_5564_ = v_isSharedCheck_5599_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_diag_5561_);
lean_inc(v_postponed_5560_);
lean_inc(v_zetaDeltaFVarIds_5559_);
lean_inc(v_mctx_5558_);
lean_dec(v___x_5557_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5599_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5565_; lean_object* v___x_5567_; 
v___x_5565_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 1, v___x_5565_);
v___x_5567_ = v___x_5563_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_mctx_5558_);
lean_ctor_set(v_reuseFailAlloc_5598_, 1, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5598_, 2, v_zetaDeltaFVarIds_5559_);
lean_ctor_set(v_reuseFailAlloc_5598_, 3, v_postponed_5560_);
lean_ctor_set(v_reuseFailAlloc_5598_, 4, v_diag_5561_);
v___x_5567_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
lean_object* v___x_5568_; lean_object* v_r_5569_; 
v___x_5568_ = lean_st_ref_put(v___y_5528_, v___x_5567_);
lean_inc(v___y_5530_);
lean_inc_ref(v___y_5529_);
lean_inc(v___y_5528_);
lean_inc_ref(v___y_5527_);
v_r_5569_ = lean_apply_5(v_x_5525_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, lean_box(0));
if (lean_obj_tag(v_r_5569_) == 0)
{
lean_object* v_a_5570_; lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5586_; 
v_a_5570_ = lean_ctor_get(v_r_5569_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v_r_5569_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5572_ = v_r_5569_;
v_isShared_5573_ = v_isSharedCheck_5586_;
goto v_resetjp_5571_;
}
else
{
lean_inc(v_a_5570_);
lean_dec(v_r_5569_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5586_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v___x_5575_; 
lean_inc(v_a_5570_);
if (v_isShared_5573_ == 0)
{
lean_ctor_set_tag(v___x_5572_, 1);
v___x_5575_ = v___x_5572_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5570_);
v___x_5575_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___x_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5583_; 
v___x_5576_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5530_, v_isExporting_5537_, v___x_5553_, v___y_5528_, v___x_5565_, v___x_5575_);
lean_dec_ref(v___x_5575_);
v_isSharedCheck_5583_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5583_ == 0)
{
lean_object* v_unused_5584_; 
v_unused_5584_ = lean_ctor_get(v___x_5576_, 0);
lean_dec(v_unused_5584_);
v___x_5578_ = v___x_5576_;
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
else
{
lean_dec(v___x_5576_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5581_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 0, v_a_5570_);
v___x_5581_ = v___x_5578_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5570_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5596_; 
v_a_5587_ = lean_ctor_get(v_r_5569_, 0);
lean_inc(v_a_5587_);
lean_dec_ref_known(v_r_5569_, 1);
v___x_5588_ = lean_box(0);
v___x_5589_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5530_, v_isExporting_5537_, v___x_5553_, v___y_5528_, v___x_5565_, v___x_5588_);
v_isSharedCheck_5596_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v___x_5589_, 0);
lean_dec(v_unused_5597_);
v___x_5591_ = v___x_5589_;
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
else
{
lean_dec(v___x_5589_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5594_; 
if (v_isShared_5592_ == 0)
{
lean_ctor_set_tag(v___x_5591_, 1);
lean_ctor_set(v___x_5591_, 0, v_a_5587_);
v___x_5594_ = v___x_5591_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5587_);
v___x_5594_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
return v___x_5594_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5606_, lean_object* v_isExporting_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_){
_start:
{
uint8_t v_isExporting_boxed_5613_; lean_object* v_res_5614_; 
v_isExporting_boxed_5613_ = lean_unbox(v_isExporting_5607_);
v_res_5614_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5606_, v_isExporting_boxed_5613_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
lean_dec(v___y_5611_);
lean_dec_ref(v___y_5610_);
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5608_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5615_, uint8_t v_when_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
if (v_when_5616_ == 0)
{
lean_object* v___x_5622_; 
lean_inc(v___y_5620_);
lean_inc_ref(v___y_5619_);
lean_inc(v___y_5618_);
lean_inc_ref(v___y_5617_);
v___x_5622_ = lean_apply_5(v_x_5615_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, lean_box(0));
return v___x_5622_;
}
else
{
uint8_t v___x_5623_; lean_object* v___x_5624_; 
v___x_5623_ = 0;
v___x_5624_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5615_, v___x_5623_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
return v___x_5624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5625_, lean_object* v_when_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
uint8_t v_when_boxed_5632_; lean_object* v_res_5633_; 
v_when_boxed_5632_ = lean_unbox(v_when_5626_);
v_res_5633_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5625_, v_when_boxed_5632_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
lean_dec(v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
return v_res_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v___x_5640_; lean_object* v_a_5641_; lean_object* v___x_5642_; uint8_t v___x_5643_; lean_object* v___x_5644_; 
v___x_5640_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5634_, v___y_5636_);
v_a_5641_ = lean_ctor_get(v___x_5640_, 0);
lean_inc(v_a_5641_);
lean_dec_ref(v___x_5640_);
v___x_5642_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5642_, 0, v_a_5641_);
v___x_5643_ = 1;
v___x_5644_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5642_, v___x_5643_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_){
_start:
{
lean_object* v_res_5651_; 
v_res_5651_ = l_Lean_Meta_letToHave___lam__0(v_e_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
lean_dec(v___y_5649_);
lean_dec_ref(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
return v_res_5651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_){
_start:
{
lean_object* v___f_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; 
v___f_5659_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5659_, 0, v_e_5653_);
v___x_5660_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5656_);
v___x_5661_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5662_ = lean_box(0);
v___x_5663_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5661_, v___x_5660_, v___f_5659_, v___x_5662_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_);
lean_dec_ref(v___x_5660_);
return v___x_5663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l_Lean_Meta_letToHave(v_e_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
lean_dec(v_a_5668_);
lean_dec_ref(v_a_5667_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5671_, lean_object* v_x_5672_, uint8_t v_when_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
lean_object* v___x_5679_; 
v___x_5679_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5672_, v_when_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5680_, lean_object* v_x_5681_, lean_object* v_when_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_){
_start:
{
uint8_t v_when_boxed_5688_; lean_object* v_res_5689_; 
v_when_boxed_5688_ = lean_unbox(v_when_5682_);
v_res_5689_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5680_, v_x_5681_, v_when_boxed_5688_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_);
lean_dec(v___y_5686_);
lean_dec_ref(v___y_5685_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5690_, lean_object* v_x_5691_, uint8_t v_isExporting_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_){
_start:
{
lean_object* v___x_5698_; 
v___x_5698_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5691_, v_isExporting_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
return v___x_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5699_, lean_object* v_x_5700_, lean_object* v_isExporting_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
uint8_t v_isExporting_boxed_5707_; lean_object* v_res_5708_; 
v_isExporting_boxed_5707_ = lean_unbox(v_isExporting_5701_);
v_res_5708_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5699_, v_x_5700_, v_isExporting_boxed_5707_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
lean_dec(v___y_5705_);
lean_dec_ref(v___y_5704_);
lean_dec(v___y_5703_);
lean_dec_ref(v___y_5702_);
return v_res_5708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5765_; uint8_t v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; 
v___x_5765_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5766_ = 0;
v___x_5767_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5768_ = l_Lean_registerTraceClass(v___x_5765_, v___x_5766_, v___x_5767_);
if (lean_obj_tag(v___x_5768_) == 0)
{
lean_object* v___x_5769_; lean_object* v___x_5770_; 
lean_dec_ref_known(v___x_5768_, 1);
v___x_5769_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5770_ = l_Lean_registerTraceClass(v___x_5769_, v___x_5766_, v___x_5767_);
return v___x_5770_;
}
else
{
return v___x_5768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5771_){
_start:
{
lean_object* v_res_5772_; 
v_res_5772_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5772_;
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
