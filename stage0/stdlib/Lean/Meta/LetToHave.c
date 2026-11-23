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
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__9;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__10;
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
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__4;
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
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1432__overap_1230_; lean_object* v___x_1231_; 
v___x_1226_ = l_StateRefT_x27_instMonad___redArg(v___x_1225_);
v___x_1227_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1228_ = l_instInhabitedOfMonad___redArg(v___x_1226_, v___x_1227_);
v___f_1229_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1229_, 0, v___x_1228_);
v___x_1432__overap_1230_ = lean_panic_fn_borrowed(v___f_1229_, v_msg_1169_);
lean_dec_ref(v___f_1229_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc(v___y_1170_);
v___x_1231_ = lean_apply_7(v___x_1432__overap_1230_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, lean_box(0));
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
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
lean_ctor_set(v___x_1258_, 2, v___x_1257_);
lean_ctor_set(v___x_1258_, 3, v___x_1257_);
lean_ctor_set(v___x_1258_, 4, v___x_1256_);
lean_ctor_set(v___x_1258_, 5, v___x_1256_);
lean_ctor_set(v___x_1258_, 6, v___x_1256_);
lean_ctor_set(v___x_1258_, 7, v___x_1256_);
lean_ctor_set(v___x_1258_, 8, v___x_1256_);
lean_ctor_set(v___x_1258_, 9, v___x_1256_);
lean_ctor_set(v___x_1258_, 10, v___x_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(32u);
v___x_1260_ = lean_mk_empty_array_with_capacity(v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1262_ = ((size_t)5ULL);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_unsigned_to_nat(32u);
v___x_1265_ = lean_mk_empty_array_with_capacity(v___x_1264_);
v___x_1266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1267_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1265_);
lean_ctor_set(v___x_1267_, 2, v___x_1263_);
lean_ctor_set(v___x_1267_, 3, v___x_1263_);
lean_ctor_set_usize(v___x_1267_, 4, v___x_1262_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1268_ = lean_box(1);
v___x_1269_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1269_);
lean_ctor_set(v___x_1271_, 2, v___x_1268_);
return v___x_1271_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1274_ = l_Lean_stringToMessageData(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1277_ = l_Lean_stringToMessageData(v___x_1276_);
return v___x_1277_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__22));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__24));
v___x_1301_ = l_Lean_stringToMessageData(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__26));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1305_, lean_object* v_declHint_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_env_1311_; uint8_t v___x_1312_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_st_ref_get(v___y_1307_);
v_env_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_ref(v_env_1311_);
lean_dec(v___x_1310_);
v___x_1312_ = l_Lean_Name_isAnonymous(v_declHint_1306_);
if (v___x_1312_ == 0)
{
uint8_t v_isExporting_1313_; 
v_isExporting_1313_ = lean_ctor_get_uint8(v_env_1311_, sizeof(void*)*13);
if (v_isExporting_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_env_1311_);
lean_dec(v_declHint_1306_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_msg_1305_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
lean_inc_ref(v_env_1311_);
v___x_1315_ = l_Lean_Environment_setExporting(v_env_1311_, v___x_1312_);
lean_inc(v_declHint_1306_);
lean_inc_ref(v___x_1315_);
v___x_1316_ = l_Lean_Environment_contains(v___x_1315_, v_declHint_1306_, v_isExporting_1313_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref(v___x_1315_);
lean_dec_ref(v_env_1311_);
lean_dec(v_declHint_1306_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_msg_1305_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v_c_1323_; lean_object* v___x_1324_; 
v___x_1318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1320_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1315_);
v___x_1321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1315_);
lean_ctor_set(v___x_1321_, 1, v___x_1318_);
lean_ctor_set(v___x_1321_, 2, v___x_1319_);
lean_ctor_set(v___x_1321_, 3, v___x_1320_);
lean_inc(v_declHint_1306_);
v___x_1322_ = l_Lean_MessageData_ofConstName(v_declHint_1306_, v___x_1312_);
v_c_1323_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1323_, 0, v___x_1321_);
lean_ctor_set(v_c_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1315_, v_declHint_1306_);
lean_dec_ref(v___x_1315_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v_env_1311_);
lean_dec(v_declHint_1306_);
v___x_1325_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_c_1323_);
v___x_1327_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_MessageData_note(v___x_1328_);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_msg_1305_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
else
{
lean_object* v_val_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1385_; 
v_val_1332_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1334_ = v___x_1324_;
v_isShared_1335_ = v_isSharedCheck_1385_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_val_1332_);
lean_dec(v___x_1324_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1385_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v_modules_1337_; lean_object* v_moduleNames_1338_; lean_object* v_mod_1339_; uint8_t v___x_1354_; 
v___x_1336_ = l_Lean_Environment_header(v_env_1311_);
lean_dec_ref(v_env_1311_);
v_modules_1337_ = lean_ctor_get(v___x_1336_, 3);
lean_inc_ref(v_modules_1337_);
v_moduleNames_1338_ = lean_ctor_get(v___x_1336_, 4);
lean_inc_ref(v_moduleNames_1338_);
lean_dec_ref(v___x_1336_);
v_mod_1339_ = lean_array_get(v___x_1309_, v_moduleNames_1338_, v_val_1332_);
lean_dec_ref(v_moduleNames_1338_);
v___x_1354_ = l_Lean_isPrivateName(v_declHint_1306_);
lean_dec(v_declHint_1306_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_array_get_size(v_modules_1337_);
v___x_1356_ = lean_nat_dec_lt(v_val_1332_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_dec_ref(v_modules_1337_);
lean_dec(v_val_1332_);
goto v___jp_1340_;
}
else
{
lean_object* v___x_1357_; lean_object* v_toImport_1358_; uint8_t v_isExported_1359_; 
v___x_1357_ = lean_array_fget(v_modules_1337_, v_val_1332_);
lean_dec(v_val_1332_);
lean_dec_ref(v_modules_1337_);
v_toImport_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc_ref(v_toImport_1358_);
lean_dec(v___x_1357_);
v_isExported_1359_ = lean_ctor_get_uint8(v_toImport_1358_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1358_);
if (v_isExported_1359_ == 0)
{
goto v___jp_1340_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_del_object(v___x_1334_);
v___x_1360_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v_c_1323_);
v___x_1362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_MessageData_ofName(v_mod_1339_);
lean_inc_ref(v___x_1364_);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___x_1364_);
v___x_1369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__23);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l_Lean_MessageData_note(v___x_1370_);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_msg_1305_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec_ref(v_modules_1337_);
lean_del_object(v___x_1334_);
lean_dec(v_val_1332_);
v___x_1374_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v_c_1323_);
v___x_1376_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__25);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_MessageData_ofName(v_mod_1339_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__27);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_MessageData_note(v___x_1381_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_msg_1305_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
v___jp_1340_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_c_1323_);
v___x_1343_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_MessageData_ofName(v_mod_1339_);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_MessageData_note(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_msg_1305_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1350_);
v___x_1352_ = v___x_1334_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1386_; 
lean_dec_ref(v_env_1311_);
lean_dec(v_declHint_1306_);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_msg_1305_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1387_, lean_object* v_declHint_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1387_, v_declHint_1388_, v___y_1389_);
lean_dec(v___y_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1392_, lean_object* v_declHint_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1411_; 
v___x_1401_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1392_, v_declHint_1393_, v___y_1399_);
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = l_Lean_unknownIdentifierMessageTag;
v___x_1407_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v_a_1402_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1407_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1412_, lean_object* v_declHint_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1412_, v_declHint_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v_env_1429_; uint8_t v___x_1430_; lean_object* v_env_1431_; lean_object* v___x_1432_; lean_object* v_toCold_1433_; lean_object* v_mctx_1434_; lean_object* v_lctx_1435_; lean_object* v_options_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1428_ = lean_st_ref_get(v___y_1426_);
v_env_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc_ref(v_env_1429_);
lean_dec(v___x_1428_);
v___x_1430_ = 0;
v_env_1431_ = l_Lean_Environment_setRecordingDeps(v_env_1429_, v___x_1430_);
v___x_1432_ = lean_st_ref_get(v___y_1424_);
v_toCold_1433_ = lean_ctor_get(v___y_1425_, 0);
v_mctx_1434_ = lean_ctor_get(v___x_1432_, 0);
lean_inc_ref(v_mctx_1434_);
lean_dec(v___x_1432_);
v_lctx_1435_ = lean_ctor_get(v___y_1423_, 2);
v_options_1436_ = lean_ctor_get(v_toCold_1433_, 2);
lean_inc_ref(v_options_1436_);
lean_inc_ref(v_lctx_1435_);
v___x_1437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1437_, 0, v_env_1431_);
lean_ctor_set(v___x_1437_, 1, v_mctx_1434_);
lean_ctor_set(v___x_1437_, 2, v_lctx_1435_);
lean_ctor_set(v___x_1437_, 3, v_options_1436_);
v___x_1438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v_msgData_1422_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_ref_1453_; lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1463_; 
v_ref_1453_ = lean_ctor_get(v___y_1450_, 2);
v___x_1454_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_inc(v_ref_1453_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_ref_1453_);
lean_ctor_set(v___x_1459_, 1, v_a_1455_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 1);
lean_ctor_set(v___x_1457_, 0, v___x_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_toCold_1480_; lean_object* v_currRecDepth_1481_; lean_object* v_ref_1482_; uint16_t v_optionFlags_1483_; uint8_t v_suppressElabErrors_1484_; uint8_t v_checkDeprecated_1485_; uint8_t v_isRecordingDeps_1486_; lean_object* v_ref_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_toCold_1480_ = lean_ctor_get(v___y_1477_, 0);
v_currRecDepth_1481_ = lean_ctor_get(v___y_1477_, 1);
v_ref_1482_ = lean_ctor_get(v___y_1477_, 2);
v_optionFlags_1483_ = lean_ctor_get_uint16(v___y_1477_, sizeof(void*)*3);
v_suppressElabErrors_1484_ = lean_ctor_get_uint8(v___y_1477_, sizeof(void*)*3 + 2);
v_checkDeprecated_1485_ = lean_ctor_get_uint8(v___y_1477_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1486_ = lean_ctor_get_uint8(v___y_1477_, sizeof(void*)*3 + 4);
v_ref_1487_ = l_Lean_replaceRef(v_ref_1471_, v_ref_1482_);
lean_inc(v_currRecDepth_1481_);
lean_inc_ref(v_toCold_1480_);
v___x_1488_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1488_, 0, v_toCold_1480_);
lean_ctor_set(v___x_1488_, 1, v_currRecDepth_1481_);
lean_ctor_set(v___x_1488_, 2, v_ref_1487_);
lean_ctor_set_uint16(v___x_1488_, sizeof(void*)*3, v_optionFlags_1483_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*3 + 2, v_suppressElabErrors_1484_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*3 + 3, v_checkDeprecated_1485_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*3 + 4, v_isRecordingDeps_1486_);
v___x_1489_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1472_, v___y_1475_, v___y_1476_, v___x_1488_, v___y_1478_);
lean_dec_ref_known(v___x_1488_, 3);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1490_, lean_object* v_msg_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1490_, v_msg_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v_ref_1490_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1500_, lean_object* v_msg_1501_, lean_object* v_declHint_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_a_1511_; lean_object* v___x_1512_; 
v___x_1510_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1501_, v_declHint_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1510_);
v___x_1512_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1500_, v_a_1511_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1513_, lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1513_, v_msg_1514_, v_declHint_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec(v_ref_1513_);
return v_res_1523_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1530_, lean_object* v_constName_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1539_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1540_ = 0;
lean_inc(v_constName_1531_);
v___x_1541_ = l_Lean_MessageData_ofConstName(v_constName_1531_, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1539_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1530_, v___x_1544_, v_constName_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1546_, lean_object* v_constName_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1546_, v_constName_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v_ref_1546_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_ref_1564_; lean_object* v___x_1565_; 
v_ref_1564_ = lean_ctor_get(v___y_1561_, 2);
v___x_1565_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1564_, v_constName_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec(v___y_1567_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v_env_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = lean_st_ref_get(v___y_1581_);
v_env_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc_ref(v_env_1584_);
lean_dec(v___x_1583_);
v___x_1585_ = 0;
lean_inc(v_constName_1575_);
v___x_1586_ = l_Lean_Environment_findConstVal_x3f(v_env_1584_, v_constName_1575_, v___x_1585_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
return v___x_1587_;
}
else
{
lean_object* v_val_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_constName_1575_);
v_val_1588_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1586_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_val_1588_);
lean_dec(v___x_1586_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 0);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_val_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec(v___y_1597_);
return v_res_1604_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1609_ = lean_unsigned_to_nat(35u);
v___x_1610_ = lean_unsigned_to_nat(203u);
v___x_1611_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1612_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1613_ = l_mkPanicMessageWithDecl(v___x_1612_, v___x_1611_, v___x_1610_, v___x_1609_, v___x_1608_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
if (lean_obj_tag(v_e_1614_) == 4)
{
lean_object* v_declName_1622_; lean_object* v_us_1623_; lean_object* v___x_1624_; 
v_declName_1622_ = lean_ctor_get(v_e_1614_, 0);
v_us_1623_ = lean_ctor_get(v_e_1614_, 1);
lean_inc(v_declName_1622_);
v___x_1624_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1622_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_levelParams_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_levelParams_1626_ = lean_ctor_get(v_a_1625_, 1);
v___x_1627_ = l_List_lengthTR___redArg(v_levelParams_1626_);
v___x_1628_ = l_List_lengthTR___redArg(v_us_1623_);
v___x_1629_ = lean_nat_dec_eq(v___x_1627_, v___x_1628_);
lean_dec(v___x_1628_);
lean_dec(v___x_1627_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_inc(v_us_1623_);
lean_inc(v_declName_1622_);
lean_dec(v_a_1625_);
lean_dec_ref_known(v_e_1614_, 2);
v___x_1630_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1622_, v_us_1623_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; 
lean_inc(v_us_1623_);
v___x_1631_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1625_, v_us_1623_, v___y_1620_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1641_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1641_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1641_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_a_1632_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_e_1614_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1637_);
v___x_1639_ = v___x_1634_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref_known(v_e_1614_, 2);
v_a_1642_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1631_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1631_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref_known(v_e_1614_, 2);
v_a_1650_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1624_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1624_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec_ref(v_e_1614_);
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1659_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1658_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___y_1677_; lean_object* v___x_1678_; 
lean_inc_ref(v_e_1669_);
v___y_1677_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1677_, 0, v_e_1669_);
v___x_1678_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1669_, v___y_1677_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec(v_a_1680_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1688_, lean_object* v_constName_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1698_, lean_object* v_constName_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1698_, v_constName_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1708_, lean_object* v_ref_1709_, lean_object* v_constName_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1709_, v_constName_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_ref_1720_, lean_object* v_constName_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1719_, v_ref_1720_, v_constName_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v_ref_1720_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1730_, lean_object* v_ref_1731_, lean_object* v_msg_1732_, lean_object* v_declHint_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1731_, v_msg_1732_, v_declHint_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_ref_1743_, lean_object* v_msg_1744_, lean_object* v_declHint_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1742_, v_ref_1743_, v_msg_1744_, v_declHint_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec(v_ref_1743_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1754_, lean_object* v_declHint_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1754_, v_declHint_1755_, v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1764_, lean_object* v_declHint_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1764_, v_declHint_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1774_, lean_object* v_ref_1775_, lean_object* v_msg_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1775_, v_msg_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_ref_1786_, lean_object* v_msg_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1785_, v_ref_1786_, v_msg_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec(v_ref_1786_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1796_, lean_object* v_msg_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1797_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1806_, lean_object* v_msg_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1806_, v_msg_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec(v___y_1808_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1817_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_r_1816_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; 
lean_inc_ref(v_r_1816_);
v___x_1826_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1816_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1879_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1879_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1879_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_expr_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1877_; 
v_expr_1831_ = lean_ctor_get(v_r_1816_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_r_1816_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v_r_1816_, 1);
lean_dec(v_unused_1878_);
v___x_1833_ = v_r_1816_;
v_isShared_1834_ = v_isSharedCheck_1877_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_expr_1831_);
lean_dec(v_r_1816_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1877_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Expr_isSort(v_a_1827_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_del_object(v___x_1829_);
lean_inc(v_a_1822_);
lean_inc_ref(v_a_1821_);
lean_inc(v_a_1820_);
lean_inc_ref(v_a_1819_);
v___x_1836_ = lean_whnf(v_a_1827_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1861_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1861_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1861_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 3)
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_a_1837_);
lean_inc_ref(v_expr_1831_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1841_);
v___x_1843_ = v___x_1833_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_expr_1831_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v_count_1845_; lean_object* v_results_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1858_; 
v___x_1844_ = lean_st_ref_take(v_a_1818_);
v_count_1845_ = lean_ctor_get(v___x_1844_, 0);
v_results_1846_ = lean_ctor_get(v___x_1844_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1848_ = v___x_1844_;
v_isShared_1849_ = v_isSharedCheck_1858_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_results_1846_);
lean_inc(v_count_1845_);
lean_dec(v___x_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1858_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_inc_ref(v___x_1843_);
v___x_1850_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1846_, v_expr_1831_, v___x_1843_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_count_1845_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_st_ref_put(v_a_1818_, v___x_1852_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1843_);
v___x_1855_ = v___x_1839_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1843_);
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
else
{
lean_object* v___x_1860_; 
lean_del_object(v___x_1839_);
lean_dec(v_a_1837_);
lean_del_object(v___x_1833_);
v___x_1860_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1831_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_del_object(v___x_1833_);
lean_dec_ref(v_expr_1831_);
v_a_1862_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1836_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1836_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_a_1827_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1870_);
v___x_1872_ = v___x_1833_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_expr_1831_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1874_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1872_);
v___x_1874_ = v___x_1829_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
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
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_r_1816_);
v_a_1880_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1826_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1826_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec(v_a_1889_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = l_Lean_instInhabitedExpr;
v___x_1899_ = lean_panic_fn_borrowed(v___x_1898_, v_msg_1897_);
return v___x_1899_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1904_ = lean_unsigned_to_nat(18u);
v___x_1905_ = lean_unsigned_to_nat(1913u);
v___x_1906_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1908_ = l_mkPanicMessageWithDecl(v___x_1907_, v___x_1906_, v___x_1905_, v___x_1904_, v___x_1903_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1909_, lean_object* v_f_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___y_1920_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1933_; lean_object* v_fType_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v___x_1994_; 
v___x_1994_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1912_);
if (v___x_1994_ == 0)
{
if (lean_obj_tag(v_e_1909_) == 5)
{
lean_object* v_expr_1995_; lean_object* v_expr_1996_; lean_object* v_fn_1997_; lean_object* v_arg_1998_; size_t v___x_1999_; size_t v___x_2000_; uint8_t v___x_2001_; 
v_expr_1995_ = lean_ctor_get(v_f_1910_, 0);
lean_inc_ref(v_expr_1995_);
lean_dec_ref(v_f_1910_);
v_expr_1996_ = lean_ctor_get(v_a_1911_, 0);
lean_inc_ref(v_expr_1996_);
lean_dec_ref(v_a_1911_);
v_fn_1997_ = lean_ctor_get(v_e_1909_, 0);
v_arg_1998_ = lean_ctor_get(v_e_1909_, 1);
v___x_1999_ = lean_ptr_addr(v_fn_1997_);
v___x_2000_ = lean_ptr_addr(v_expr_1995_);
v___x_2001_ = lean_usize_dec_eq(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec_ref_known(v_e_1909_, 2);
v___x_2002_ = l_Lean_Expr_app___override(v_expr_1995_, v_expr_1996_);
v___y_1920_ = v___x_2002_;
goto v___jp_1919_;
}
else
{
size_t v___x_2003_; size_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = lean_ptr_addr(v_arg_1998_);
v___x_2004_ = lean_ptr_addr(v_expr_1996_);
v___x_2005_ = lean_usize_dec_eq(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec_ref_known(v_e_1909_, 2);
v___x_2006_ = l_Lean_Expr_app___override(v_expr_1995_, v_expr_1996_);
v___y_1920_ = v___x_2006_;
goto v___jp_1919_;
}
else
{
lean_dec_ref(v_expr_1996_);
lean_dec_ref(v_expr_1995_);
v___y_1920_ = v_e_1909_;
goto v___jp_1919_;
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec_ref(v_a_1911_);
lean_dec_ref(v_f_1910_);
lean_dec_ref(v_e_1909_);
v___x_2007_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_2008_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2007_);
v___y_1920_ = v___x_2008_;
goto v___jp_1919_;
}
}
else
{
lean_object* v___x_2009_; 
lean_inc_ref(v_f_1910_);
v___x_2009_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1910_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; uint8_t v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = l_Lean_Expr_isForall(v_a_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_inc(v_a_1917_);
lean_inc_ref(v_a_1916_);
lean_inc(v_a_1915_);
lean_inc_ref(v_a_1914_);
v___x_2012_ = lean_whnf(v_a_2010_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v_fType_1950_ = v_a_2013_;
v___y_1951_ = v_a_1913_;
v___y_1952_ = v_a_1914_;
v___y_1953_ = v_a_1915_;
v___y_1954_ = v_a_1916_;
v___y_1955_ = v_a_1917_;
goto v___jp_1949_;
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v_a_1911_);
lean_dec_ref(v_f_1910_);
lean_dec_ref(v_e_1909_);
v_a_2014_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2012_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2012_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
v_fType_1950_ = v_a_2010_;
v___y_1951_ = v_a_1913_;
v___y_1952_ = v_a_1914_;
v___y_1953_ = v_a_1915_;
v___y_1954_ = v_a_1916_;
v___y_1955_ = v_a_1917_;
goto v___jp_1949_;
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_a_1911_);
lean_dec_ref(v_f_1910_);
lean_dec_ref(v_e_1909_);
v_a_2022_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2009_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2009_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
v___jp_1924_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1928_ = lean_expr_instantiate1(v___y_1925_, v___y_1926_);
lean_dec_ref(v___y_1926_);
lean_dec_ref(v___y_1925_);
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___y_1927_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
v___jp_1932_:
{
if (lean_obj_tag(v_e_1909_) == 5)
{
lean_object* v_expr_1934_; lean_object* v_expr_1935_; lean_object* v_fn_1936_; lean_object* v_arg_1937_; size_t v___x_1938_; size_t v___x_1939_; uint8_t v___x_1940_; 
v_expr_1934_ = lean_ctor_get(v_f_1910_, 0);
lean_inc_ref(v_expr_1934_);
lean_dec_ref(v_f_1910_);
v_expr_1935_ = lean_ctor_get(v_a_1911_, 0);
lean_inc_ref(v_expr_1935_);
lean_dec_ref(v_a_1911_);
v_fn_1936_ = lean_ctor_get(v_e_1909_, 0);
v_arg_1937_ = lean_ctor_get(v_e_1909_, 1);
v___x_1938_ = lean_ptr_addr(v_fn_1936_);
v___x_1939_ = lean_ptr_addr(v_expr_1934_);
v___x_1940_ = lean_usize_dec_eq(v___x_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref_known(v_e_1909_, 2);
lean_inc_ref(v_expr_1935_);
v___x_1941_ = l_Lean_Expr_app___override(v_expr_1934_, v_expr_1935_);
v___y_1925_ = v___y_1933_;
v___y_1926_ = v_expr_1935_;
v___y_1927_ = v___x_1941_;
goto v___jp_1924_;
}
else
{
size_t v___x_1942_; size_t v___x_1943_; uint8_t v___x_1944_; 
v___x_1942_ = lean_ptr_addr(v_arg_1937_);
v___x_1943_ = lean_ptr_addr(v_expr_1935_);
v___x_1944_ = lean_usize_dec_eq(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref_known(v_e_1909_, 2);
lean_inc_ref(v_expr_1935_);
v___x_1945_ = l_Lean_Expr_app___override(v_expr_1934_, v_expr_1935_);
v___y_1925_ = v___y_1933_;
v___y_1926_ = v_expr_1935_;
v___y_1927_ = v___x_1945_;
goto v___jp_1924_;
}
else
{
lean_dec_ref(v_expr_1934_);
v___y_1925_ = v___y_1933_;
v___y_1926_ = v_expr_1935_;
v___y_1927_ = v_e_1909_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v_expr_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec_ref(v_f_1910_);
lean_dec_ref(v_e_1909_);
v_expr_1946_ = lean_ctor_get(v_a_1911_, 0);
lean_inc_ref(v_expr_1946_);
lean_dec_ref(v_a_1911_);
v___x_1947_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1948_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1947_);
v___y_1925_ = v___y_1933_;
v___y_1926_ = v_expr_1946_;
v___y_1927_ = v___x_1948_;
goto v___jp_1924_;
}
}
v___jp_1949_:
{
if (lean_obj_tag(v_fType_1950_) == 7)
{
lean_object* v_binderType_1956_; lean_object* v_body_1957_; lean_object* v___x_1958_; 
v_binderType_1956_ = lean_ctor_get(v_fType_1950_, 1);
lean_inc_ref(v_binderType_1956_);
v_body_1957_ = lean_ctor_get(v_fType_1950_, 2);
lean_inc_ref(v_body_1957_);
lean_dec_ref_known(v_fType_1950_, 3);
lean_inc_ref(v_a_1911_);
v___x_1958_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1911_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l_Lean_Meta_isExprDefEq(v_binderType_1956_, v_a_1959_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; uint8_t v___x_1962_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = lean_unbox(v_a_1961_);
lean_dec(v_a_1961_);
if (v___x_1962_ == 0)
{
lean_object* v_expr_1963_; lean_object* v_expr_1964_; lean_object* v___x_1965_; 
v_expr_1963_ = lean_ctor_get(v_f_1910_, 0);
v_expr_1964_ = lean_ctor_get(v_a_1911_, 0);
lean_inc_ref(v_expr_1964_);
lean_inc_ref(v_expr_1963_);
v___x_1965_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1963_, v_expr_1964_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref_known(v___x_1965_, 1);
v___y_1933_ = v_body_1957_;
goto v___jp_1932_;
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_a_1911_);
lean_dec_ref(v_f_1910_);
lean_dec_ref(v_e_1909_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
v___y_1933_ = v_body_1957_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_a_1911_);
lean_dec_ref(v_f_1910_);
lean_dec_ref(v_e_1909_);
v_a_1974_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1960_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1960_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_binderType_1956_);
lean_dec_ref(v_a_1911_);
lean_dec_ref(v_f_1910_);
lean_dec_ref(v_e_1909_);
v_a_1982_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1958_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1958_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v_expr_1990_; lean_object* v_expr_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_dec_ref(v_fType_1950_);
lean_dec_ref(v_e_1909_);
v_expr_1990_ = lean_ctor_get(v_f_1910_, 0);
lean_inc_ref(v_expr_1990_);
lean_dec_ref(v_f_1910_);
v_expr_1991_ = lean_ctor_get(v_a_1911_, 0);
lean_inc_ref(v_expr_1991_);
lean_dec_ref(v_a_1911_);
v___x_1992_ = l_Lean_Expr_app___override(v_expr_1990_, v_expr_1991_);
v___x_1993_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1992_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2030_, lean_object* v_f_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2030_, v_f_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec(v_a_2033_);
return v_res_2040_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2042_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2043_ = lean_unsigned_to_nat(37u);
v___x_2044_ = lean_unsigned_to_nat(345u);
v___x_2045_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2046_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2047_ = l_mkPanicMessageWithDecl(v___x_2046_, v___x_2045_, v___x_2044_, v___x_2043_, v___x_2042_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2048_, lean_object* v_i_2049_, lean_object* v_a_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_zero_2058_; uint8_t v_isZero_2059_; 
v_zero_2058_ = lean_unsigned_to_nat(0u);
v_isZero_2059_ = lean_nat_dec_eq(v_i_2049_, v_zero_2058_);
if (v_isZero_2059_ == 1)
{
lean_object* v___x_2060_; 
lean_dec(v_i_2049_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_a_2050_);
return v___x_2060_;
}
else
{
lean_object* v_one_2061_; lean_object* v_n_2062_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2073_; lean_object* v___x_2076_; 
v_one_2061_ = lean_unsigned_to_nat(1u);
v_n_2062_ = lean_nat_sub(v_i_2049_, v_one_2061_);
lean_dec(v_i_2049_);
v___x_2076_ = lean_array_fget_borrowed(v_fvars_2048_, v_n_2062_);
if (lean_obj_tag(v___x_2076_) == 1)
{
lean_object* v_fvarId_2077_; lean_object* v___x_2078_; 
v_fvarId_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_fvarId_2077_);
v___x_2078_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2077_, v___y_2053_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
if (lean_obj_tag(v_a_2079_) == 1)
{
lean_object* v_val_2080_; 
v_val_2080_ = lean_ctor_get(v_a_2079_, 0);
lean_inc(v_val_2080_);
lean_dec_ref_known(v_a_2079_, 1);
if (lean_obj_tag(v_val_2080_) == 0)
{
lean_object* v_userName_2081_; lean_object* v_type_2082_; uint8_t v_bi_2083_; lean_object* v_expr_2084_; lean_object* v_type_x3f_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2106_; 
v_userName_2081_ = lean_ctor_get(v_val_2080_, 2);
lean_inc(v_userName_2081_);
v_type_2082_ = lean_ctor_get(v_val_2080_, 3);
lean_inc_ref(v_type_2082_);
v_bi_2083_ = lean_ctor_get_uint8(v_val_2080_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2080_, 4);
v_expr_2084_ = lean_ctor_get(v_a_2050_, 0);
v_type_x3f_2085_ = lean_ctor_get(v_a_2050_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_a_2050_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2087_ = v_a_2050_;
v_isShared_2088_ = v_isSharedCheck_2106_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_type_x3f_2085_);
lean_inc(v_expr_2084_);
lean_dec(v_a_2050_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2106_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___y_2092_; 
v___x_2089_ = lean_expr_abstract_range(v_type_2082_, v_n_2062_, v_fvars_2048_);
lean_dec_ref(v_type_2082_);
lean_inc_ref(v___x_2089_);
lean_inc(v_userName_2081_);
v___x_2090_ = l_Lean_Expr_lam___override(v_userName_2081_, v___x_2089_, v_expr_2084_, v_bi_2083_);
if (lean_obj_tag(v_type_x3f_2085_) == 0)
{
lean_dec_ref(v___x_2089_);
lean_dec(v_userName_2081_);
v___y_2092_ = v_type_x3f_2085_;
goto v___jp_2091_;
}
else
{
lean_object* v_val_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
v_val_2097_ = lean_ctor_get(v_type_x3f_2085_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_type_x3f_2085_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2099_ = v_type_x3f_2085_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_val_2097_);
lean_dec(v_type_x3f_2085_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = l_Lean_Expr_forallE___override(v_userName_2081_, v___x_2089_, v_val_2097_, v_bi_2083_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2101_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
v___y_2092_ = v___x_2103_;
goto v___jp_2091_;
}
}
}
v___jp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___y_2092_);
lean_ctor_set(v___x_2087_, 0, v___x_2090_);
v___x_2094_ = v___x_2087_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___y_2092_);
v___x_2094_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
v_i_2049_ = v_n_2062_;
v_a_2050_ = v___x_2094_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2107_; lean_object* v_type_2108_; lean_object* v_value_2109_; uint8_t v_nondep_2110_; uint8_t v_nondep_2112_; lean_object* v___x_2122_; 
v_userName_2107_ = lean_ctor_get(v_val_2080_, 2);
lean_inc(v_userName_2107_);
v_type_2108_ = lean_ctor_get(v_val_2080_, 3);
lean_inc_ref(v_type_2108_);
v_value_2109_ = lean_ctor_get(v_val_2080_, 4);
lean_inc_ref(v_value_2109_);
v_nondep_2110_ = lean_ctor_get_uint8(v_val_2080_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2080_, 5);
v___x_2122_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2054_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; uint8_t v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = 1;
if (v_nondep_2110_ == 0)
{
uint8_t v___x_2125_; 
v___x_2125_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2077_, v_a_2123_);
lean_dec(v_a_2123_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2052_);
lean_dec_ref(v___x_2126_);
v_nondep_2112_ = v___x_2124_;
goto v___jp_2111_;
}
else
{
v_nondep_2112_ = v_nondep_2110_;
goto v___jp_2111_;
}
}
else
{
lean_dec(v_a_2123_);
v_nondep_2112_ = v___x_2124_;
goto v___jp_2111_;
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_value_2109_);
lean_dec_ref(v_type_2108_);
lean_dec(v_userName_2107_);
lean_dec(v_n_2062_);
lean_dec_ref(v_a_2050_);
v_a_2127_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2122_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2122_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
v___jp_2111_:
{
lean_object* v_expr_2113_; lean_object* v_type_x3f_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_expr_2113_ = lean_ctor_get(v_a_2050_, 0);
lean_inc_ref(v_expr_2113_);
v_type_x3f_2114_ = lean_ctor_get(v_a_2050_, 1);
lean_inc(v_type_x3f_2114_);
lean_dec_ref(v_a_2050_);
v___x_2115_ = lean_expr_abstract_range(v_type_2108_, v_n_2062_, v_fvars_2048_);
lean_dec_ref(v_type_2108_);
v___x_2116_ = lean_expr_abstract_range(v_value_2109_, v_n_2062_, v_fvars_2048_);
lean_dec_ref(v_value_2109_);
lean_inc_ref(v___x_2116_);
lean_inc_ref(v___x_2115_);
lean_inc(v_userName_2107_);
v___x_2117_ = l_Lean_Expr_letE___override(v_userName_2107_, v___x_2115_, v___x_2116_, v_expr_2113_, v_nondep_2112_);
if (lean_obj_tag(v_type_x3f_2114_) == 0)
{
lean_dec_ref(v___x_2116_);
lean_dec_ref(v___x_2115_);
lean_dec(v_userName_2107_);
v___y_2064_ = v___x_2117_;
v___y_2065_ = v_type_x3f_2114_;
goto v___jp_2063_;
}
else
{
lean_object* v_val_2118_; uint8_t v___x_2119_; 
v_val_2118_ = lean_ctor_get(v_type_x3f_2114_, 0);
lean_inc(v_val_2118_);
lean_dec_ref_known(v_type_x3f_2114_, 1);
v___x_2119_ = lean_expr_has_loose_bvar(v_val_2118_, v_zero_2058_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_dec_ref(v___x_2116_);
lean_dec_ref(v___x_2115_);
lean_dec(v_userName_2107_);
v___x_2120_ = lean_expr_lower_loose_bvars(v_val_2118_, v_one_2061_, v_one_2061_);
lean_dec(v_val_2118_);
v___y_2069_ = v___x_2117_;
v___y_2070_ = v___x_2120_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Expr_letE___override(v_userName_2107_, v___x_2115_, v___x_2116_, v_val_2118_, v_nondep_2112_);
v___y_2069_ = v___x_2117_;
v___y_2070_ = v___x_2121_;
goto v___jp_2068_;
}
}
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2050_);
lean_inc(v_fvarId_2077_);
v___x_2135_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2077_, v___y_2055_, v___y_2056_);
v___y_2073_ = v___x_2135_;
goto v___jp_2072_;
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_n_2062_);
lean_dec_ref(v_a_2050_);
v_a_2136_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2078_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2078_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v_a_2050_);
v___x_2144_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2145_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2144_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
v___y_2073_ = v___x_2145_;
goto v___jp_2072_;
}
v___jp_2063_:
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___y_2064_);
lean_ctor_set(v___x_2066_, 1, v___y_2065_);
v_i_2049_ = v_n_2062_;
v_a_2050_ = v___x_2066_;
goto _start;
}
v___jp_2068_:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___y_2070_);
v___y_2064_ = v___y_2069_;
v___y_2065_ = v___x_2071_;
goto v___jp_2063_;
}
v___jp_2072_:
{
if (lean_obj_tag(v___y_2073_) == 0)
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___y_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___y_2073_, 1);
v_i_2049_ = v_n_2062_;
v_a_2050_ = v_a_2074_;
goto _start;
}
else
{
lean_dec(v_n_2062_);
return v___y_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2146_, lean_object* v_i_2147_, lean_object* v_a_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2146_, v_i_2147_, v_a_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v_fvars_2146_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
if (lean_obj_tag(v_a_2157_) == 0)
{
lean_object* v___x_2159_; 
v___x_2159_ = l_List_reverse___redArg(v_a_2158_);
return v___x_2159_;
}
else
{
lean_object* v_head_2160_; lean_object* v_tail_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2170_; 
v_head_2160_ = lean_ctor_get(v_a_2157_, 0);
v_tail_2161_ = lean_ctor_get(v_a_2157_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_a_2157_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2163_ = v_a_2157_;
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_tail_2161_);
lean_inc(v_head_2160_);
lean_dec(v_a_2157_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = l_Lean_MessageData_ofExpr(v_head_2160_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v_a_2158_);
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_a_2158_);
v___x_2167_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
v_a_2157_ = v_tail_2161_;
v_a_2158_ = v___x_2167_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2171_; double v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_float_of_nat(v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2176_, lean_object* v_msg_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_ref_2183_; lean_object* v___x_2184_; lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2230_; 
v_ref_2183_ = lean_ctor_get(v___y_2180_, 2);
v___x_2184_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2230_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2230_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v_traceState_2190_; lean_object* v_env_2191_; lean_object* v_nextMacroScope_2192_; lean_object* v_ngen_2193_; lean_object* v_auxDeclNGen_2194_; lean_object* v_cache_2195_; lean_object* v_recordedDeps_2196_; lean_object* v_messages_2197_; lean_object* v_infoState_2198_; lean_object* v_snapshotTasks_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2229_; 
v___x_2189_ = lean_st_ref_take(v___y_2181_);
v_traceState_2190_ = lean_ctor_get(v___x_2189_, 4);
v_env_2191_ = lean_ctor_get(v___x_2189_, 0);
v_nextMacroScope_2192_ = lean_ctor_get(v___x_2189_, 1);
v_ngen_2193_ = lean_ctor_get(v___x_2189_, 2);
v_auxDeclNGen_2194_ = lean_ctor_get(v___x_2189_, 3);
v_cache_2195_ = lean_ctor_get(v___x_2189_, 5);
v_recordedDeps_2196_ = lean_ctor_get(v___x_2189_, 6);
v_messages_2197_ = lean_ctor_get(v___x_2189_, 7);
v_infoState_2198_ = lean_ctor_get(v___x_2189_, 8);
v_snapshotTasks_2199_ = lean_ctor_get(v___x_2189_, 9);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2201_ = v___x_2189_;
v_isShared_2202_ = v_isSharedCheck_2229_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_snapshotTasks_2199_);
lean_inc(v_infoState_2198_);
lean_inc(v_messages_2197_);
lean_inc(v_recordedDeps_2196_);
lean_inc(v_cache_2195_);
lean_inc(v_traceState_2190_);
lean_inc(v_auxDeclNGen_2194_);
lean_inc(v_ngen_2193_);
lean_inc(v_nextMacroScope_2192_);
lean_inc(v_env_2191_);
lean_dec(v___x_2189_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2229_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
uint64_t v_tid_2203_; lean_object* v_traces_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2228_; 
v_tid_2203_ = lean_ctor_get_uint64(v_traceState_2190_, sizeof(void*)*1);
v_traces_2204_ = lean_ctor_get(v_traceState_2190_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_traceState_2190_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2206_ = v_traceState_2190_;
v_isShared_2207_ = v_isSharedCheck_2228_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_traces_2204_);
lean_dec(v_traceState_2190_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2228_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; double v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2211_ = 0;
v___x_2212_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2213_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2213_, 0, v_cls_2176_);
lean_ctor_set(v___x_2213_, 1, v___x_2209_);
lean_ctor_set(v___x_2213_, 2, v___x_2212_);
lean_ctor_set_float(v___x_2213_, sizeof(void*)*3, v___x_2210_);
lean_ctor_set_float(v___x_2213_, sizeof(void*)*3 + 8, v___x_2210_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*3 + 16, v___x_2211_);
v___x_2214_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2215_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v_a_2185_);
lean_ctor_set(v___x_2215_, 2, v___x_2214_);
lean_inc(v_ref_2183_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_ref_2183_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_PersistentArray_push___redArg(v_traces_2204_, v___x_2216_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2217_);
v___x_2219_ = v___x_2206_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2217_);
lean_ctor_set_uint64(v_reuseFailAlloc_2227_, sizeof(void*)*1, v_tid_2203_);
v___x_2219_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2221_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v___x_2219_);
v___x_2221_ = v___x_2201_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_env_2191_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_nextMacroScope_2192_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_ngen_2193_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_auxDeclNGen_2194_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2226_, 5, v_cache_2195_);
lean_ctor_set(v_reuseFailAlloc_2226_, 6, v_recordedDeps_2196_);
lean_ctor_set(v_reuseFailAlloc_2226_, 7, v_messages_2197_);
lean_ctor_set(v_reuseFailAlloc_2226_, 8, v_infoState_2198_);
lean_ctor_set(v_reuseFailAlloc_2226_, 9, v_snapshotTasks_2199_);
v___x_2221_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = lean_st_ref_put(v___y_2181_, v___x_2221_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2208_);
v___x_2224_ = v___x_2187_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2208_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2231_, lean_object* v_msg_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2231_, v_msg_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
return v_res_2238_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_cls_2249_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2250_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2251_ = l_Lean_Name_append(v___x_2250_, v_cls_2249_);
return v___x_2251_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2254_ = l_Lean_stringToMessageData(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2257_ = l_Lean_stringToMessageData(v___x_2256_);
return v___x_2257_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2260_ = l_Lean_stringToMessageData(v___x_2259_);
return v___x_2260_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2265_ = l_Lean_MessageData_ofFormat(v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2266_, lean_object* v_body_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v_toCold_2306_; lean_object* v_options_2307_; uint8_t v_hasTrace_2308_; 
v_toCold_2306_ = lean_ctor_get(v_a_2272_, 0);
v_options_2307_ = lean_ctor_get(v_toCold_2306_, 2);
v_hasTrace_2308_ = lean_ctor_get_uint8(v_options_2307_, sizeof(void*)*1);
if (v_hasTrace_2308_ == 0)
{
v___y_2288_ = v_a_2268_;
v___y_2289_ = v_a_2269_;
v___y_2290_ = v_a_2270_;
v___y_2291_ = v_a_2271_;
v___y_2292_ = v_a_2272_;
v___y_2293_ = v_a_2273_;
goto v___jp_2287_;
}
else
{
lean_object* v_inheritedTraceOptions_2309_; lean_object* v_cls_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v_inheritedTraceOptions_2309_ = lean_ctor_get(v_toCold_2306_, 11);
v_cls_2310_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2311_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2312_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2309_, v_options_2307_, v___x_2311_);
if (v___x_2312_ == 0)
{
v___y_2288_ = v_a_2268_;
v___y_2289_ = v_a_2269_;
v___y_2290_ = v_a_2270_;
v___y_2291_ = v_a_2271_;
v___y_2292_ = v_a_2272_;
v___y_2293_ = v_a_2273_;
goto v___jp_2287_;
}
else
{
lean_object* v_expr_2313_; lean_object* v_type_x3f_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___y_2327_; 
v_expr_2313_ = lean_ctor_get(v_body_2267_, 0);
v_type_x3f_2314_ = lean_ctor_get(v_body_2267_, 1);
v___x_2315_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2266_);
v___x_2316_ = lean_array_to_list(v_fvars_2266_);
v___x_2317_ = lean_box(0);
v___x_2318_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2316_, v___x_2317_);
v___x_2319_ = l_Lean_MessageData_ofList(v___x_2318_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2315_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
lean_inc_ref(v_expr_2313_);
v___x_2323_ = l_Lean_MessageData_ofExpr(v_expr_2313_);
v___x_2324_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
if (lean_obj_tag(v_type_x3f_2314_) == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2327_ = v___x_2340_;
goto v___jp_2326_;
}
else
{
lean_object* v_val_2341_; lean_object* v___x_2342_; 
v_val_2341_ = lean_ctor_get(v_type_x3f_2314_, 0);
lean_inc(v_val_2341_);
v___x_2342_ = l_Lean_MessageData_ofExpr(v_val_2341_);
v___y_2327_ = v___x_2342_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2325_);
lean_ctor_set(v___x_2328_, 1, v___y_2327_);
v___x_2329_ = l_Lean_indentD(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2322_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2310_, v___x_2330_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_dec_ref_known(v___x_2331_, 1);
v___y_2288_ = v_a_2268_;
v___y_2289_ = v_a_2269_;
v___y_2290_ = v_a_2270_;
v___y_2291_ = v_a_2271_;
v___y_2292_ = v_a_2272_;
v___y_2293_ = v_a_2273_;
goto v___jp_2287_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_body_2267_);
lean_dec_ref(v_fvars_2266_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
v___jp_2275_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___y_2277_);
lean_ctor_set(v___x_2284_, 1, v___y_2283_);
v___x_2285_ = lean_array_get_size(v_fvars_2266_);
v___x_2286_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2266_, v___x_2285_, v___x_2284_, v___y_2280_, v___y_2278_, v___y_2282_, v___y_2281_, v___y_2279_, v___y_2276_);
lean_dec_ref(v_fvars_2266_);
return v___x_2286_;
}
v___jp_2287_:
{
lean_object* v_expr_2294_; lean_object* v_type_x3f_2295_; lean_object* v___x_2296_; 
v_expr_2294_ = lean_ctor_get(v_body_2267_, 0);
lean_inc_ref(v_expr_2294_);
v_type_x3f_2295_ = lean_ctor_get(v_body_2267_, 1);
lean_inc(v_type_x3f_2295_);
lean_dec_ref(v_body_2267_);
v___x_2296_ = lean_expr_abstract(v_expr_2294_, v_fvars_2266_);
lean_dec_ref(v_expr_2294_);
if (lean_obj_tag(v_type_x3f_2295_) == 0)
{
v___y_2276_ = v___y_2293_;
v___y_2277_ = v___x_2296_;
v___y_2278_ = v___y_2289_;
v___y_2279_ = v___y_2292_;
v___y_2280_ = v___y_2288_;
v___y_2281_ = v___y_2291_;
v___y_2282_ = v___y_2290_;
v___y_2283_ = v_type_x3f_2295_;
goto v___jp_2275_;
}
else
{
lean_object* v_val_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2305_; 
v_val_2297_ = lean_ctor_get(v_type_x3f_2295_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_type_x3f_2295_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2299_ = v_type_x3f_2295_;
v_isShared_2300_ = v_isSharedCheck_2305_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_val_2297_);
lean_dec(v_type_x3f_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2305_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_expr_abstract(v_val_2297_, v_fvars_2266_);
lean_dec(v_val_2297_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2301_);
v___x_2303_ = v___x_2299_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
v___y_2276_ = v___y_2293_;
v___y_2277_ = v___x_2296_;
v___y_2278_ = v___y_2289_;
v___y_2279_ = v___y_2292_;
v___y_2280_ = v___y_2288_;
v___y_2281_ = v___y_2291_;
v___y_2282_ = v___y_2290_;
v___y_2283_ = v___x_2303_;
goto v___jp_2275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2343_, lean_object* v_body_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2343_, v_body_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec(v_a_2345_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2353_, lean_object* v_n_2354_, lean_object* v_i_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2353_, v_i_2355_, v_a_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2366_, lean_object* v_n_2367_, lean_object* v_i_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2366_, v_n_2367_, v_i_2368_, v_a_2369_, v_a_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v_n_2367_);
lean_dec_ref(v_fvars_2366_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2379_, lean_object* v_msg_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2379_, v_msg_2380_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2389_, lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2389_, v_msg_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec(v___y_2391_);
return v_res_2398_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2401_ = l_Lean_stringToMessageData(v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2404_ = l_Lean_stringToMessageData(v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2405_, lean_object* v_structName_2406_, lean_object* v_idx_2407_, lean_object* v_a_2408_, lean_object* v_00_u03b1_2409_, lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_expr_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2433_; 
v_expr_2418_ = lean_ctor_get(v_struct_2405_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_struct_2405_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v_struct_2405_, 1);
lean_dec(v_unused_2434_);
v___x_2420_ = v_struct_2405_;
v_isShared_2421_ = v_isSharedCheck_2433_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_expr_2418_);
lean_dec(v_struct_2405_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2433_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2422_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2423_ = l_Lean_mkProj(v_structName_2406_, v_idx_2407_, v_expr_2418_);
v___x_2424_ = l_Lean_indentExpr(v___x_2423_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 7);
lean_ctor_set(v___x_2420_, 1, v___x_2424_);
lean_ctor_set(v___x_2420_, 0, v___x_2422_);
v___x_2426_ = v___x_2420_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2427_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = l_Lean_indentExpr(v_a_2408_);
v___x_2430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2430_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2435_, lean_object* v_structName_2436_, lean_object* v_idx_2437_, lean_object* v_a_2438_, lean_object* v_00_u03b1_2439_, lean_object* v_x_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2435_, v_structName_2436_, v_idx_2437_, v_a_2438_, v_00_u03b1_2439_, v_x_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec(v___y_2441_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v_env_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2457_ = lean_st_ref_get(v___y_2455_);
v_env_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc_ref(v_env_2458_);
lean_dec(v___x_2457_);
v___x_2459_ = 0;
lean_inc(v_constName_2449_);
v___x_2460_ = l_Lean_Environment_find_x3f(v_env_2458_, v_constName_2449_, v___x_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
return v___x_2461_;
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_constName_2449_);
v_val_2462_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2460_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_val_2462_);
lean_dec(v___x_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 0);
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_val_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec(v___y_2471_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2479_, lean_object* v_structName_2480_, lean_object* v_idx_2481_, lean_object* v_a_2482_, lean_object* v_00_u03b1_2483_, lean_object* v_x_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_expr_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2507_; 
v_expr_2492_ = lean_ctor_get(v_struct_2479_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_struct_2479_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v_struct_2479_, 1);
lean_dec(v_unused_2508_);
v___x_2494_ = v_struct_2479_;
v_isShared_2495_ = v_isSharedCheck_2507_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_expr_2492_);
lean_dec(v_struct_2479_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2507_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2496_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2497_ = l_Lean_mkProj(v_structName_2480_, v_idx_2481_, v_expr_2492_);
v___x_2498_ = l_Lean_indentExpr(v___x_2497_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 7);
lean_ctor_set(v___x_2494_, 1, v___x_2498_);
lean_ctor_set(v___x_2494_, 0, v___x_2496_);
v___x_2500_ = v___x_2494_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2501_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = l_Lean_indentExpr(v_a_2482_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2504_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2509_, lean_object* v_structName_2510_, lean_object* v_idx_2511_, lean_object* v_a_2512_, lean_object* v_00_u03b1_2513_, lean_object* v_x_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2509_, v_structName_2510_, v_idx_2511_, v_a_2512_, v_00_u03b1_2513_, v_x_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2523_, lean_object* v_fst_2524_, lean_object* v_struct_2525_, lean_object* v_structName_2526_, uint8_t v_a_2527_, lean_object* v___f_2528_, lean_object* v_snd_2529_, lean_object* v_____r_2530_, lean_object* v_ctorType_2531_, lean_object* v_j_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
if (lean_obj_tag(v_ctorType_2531_) == 7)
{
lean_object* v_binderType_2540_; lean_object* v_body_2541_; lean_object* v___x_2542_; 
lean_dec(v_snd_2529_);
v_binderType_2540_ = lean_ctor_get(v_ctorType_2531_, 1);
lean_inc_ref(v_binderType_2540_);
v_body_2541_ = lean_ctor_get(v_ctorType_2531_, 2);
lean_inc_ref(v_body_2541_);
lean_dec_ref_known(v_ctorType_2531_, 3);
v___x_2542_ = lean_expr_instantiate_rev_range(v_binderType_2540_, v_j_2532_, v_a_2523_, v_fst_2524_);
lean_dec_ref(v_binderType_2540_);
if (v_a_2527_ == 0)
{
lean_dec_ref(v___f_2528_);
goto v___jp_2543_;
}
else
{
lean_object* v___x_2559_; 
lean_inc_ref(v___x_2542_);
v___x_2559_ = l_Lean_Meta_isProp(v___x_2542_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; uint8_t v___x_2561_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_box(0);
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2537_);
lean_inc(v___y_2536_);
lean_inc_ref(v___y_2535_);
lean_inc(v___y_2534_);
lean_inc(v___y_2533_);
v___x_2563_ = lean_apply_9(v___f_2528_, lean_box(0), v___x_2562_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, lean_box(0));
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_dec_ref_known(v___x_2563_, 1);
goto v___jp_2543_;
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref(v___x_2542_);
lean_dec_ref(v_body_2541_);
lean_dec(v_structName_2526_);
lean_dec_ref(v_struct_2525_);
lean_dec(v_fst_2524_);
lean_dec(v_a_2523_);
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
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
else
{
lean_dec_ref(v___f_2528_);
goto v___jp_2543_;
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v___x_2542_);
lean_dec_ref(v_body_2541_);
lean_dec_ref(v___f_2528_);
lean_dec(v_structName_2526_);
lean_dec_ref(v_struct_2525_);
lean_dec(v_fst_2524_);
lean_dec(v_a_2523_);
v_a_2572_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2559_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2559_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
v___jp_2543_:
{
lean_object* v_expr_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2557_; 
v_expr_2544_ = lean_ctor_get(v_struct_2525_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_struct_2525_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v_struct_2525_, 1);
lean_dec(v_unused_2558_);
v___x_2546_ = v_struct_2525_;
v_isShared_2547_ = v_isSharedCheck_2557_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_expr_2544_);
lean_dec(v_struct_2525_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2557_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2548_ = l_Lean_Expr_proj___override(v_structName_2526_, v_a_2523_, v_expr_2544_);
v___x_2549_ = lean_array_push(v_fst_2524_, v___x_2548_);
lean_inc(v_j_2532_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 1, v___x_2542_);
lean_ctor_set(v___x_2546_, 0, v_j_2532_);
v___x_2551_ = v___x_2546_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_j_2532_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2542_);
v___x_2551_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2549_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v_body_2541_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec(v_structName_2526_);
lean_dec_ref(v_struct_2525_);
lean_dec(v_a_2523_);
v___x_2580_ = lean_box(0);
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2537_);
lean_inc(v___y_2536_);
lean_inc_ref(v___y_2535_);
lean_inc(v___y_2534_);
lean_inc(v___y_2533_);
v___x_2581_ = lean_apply_9(v___f_2528_, lean_box(0), v___x_2580_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, lean_box(0));
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2592_; 
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2592_ == 0)
{
lean_object* v_unused_2593_; 
v_unused_2593_ = lean_ctor_get(v___x_2581_, 0);
lean_dec(v_unused_2593_);
v___x_2583_ = v___x_2581_;
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
else
{
lean_dec(v___x_2581_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_inc(v_j_2532_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v_j_2532_);
lean_ctor_set(v___x_2585_, 1, v_snd_2529_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_fst_2524_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_ctorType_2531_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2588_);
v___x_2590_ = v___x_2583_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_ctorType_2531_);
lean_dec(v_snd_2529_);
lean_dec(v_fst_2524_);
v_a_2594_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2581_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2581_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2602_ = _args[0];
lean_object* v_fst_2603_ = _args[1];
lean_object* v_struct_2604_ = _args[2];
lean_object* v_structName_2605_ = _args[3];
lean_object* v_a_2606_ = _args[4];
lean_object* v___f_2607_ = _args[5];
lean_object* v_snd_2608_ = _args[6];
lean_object* v_____r_2609_ = _args[7];
lean_object* v_ctorType_2610_ = _args[8];
lean_object* v_j_2611_ = _args[9];
lean_object* v___y_2612_ = _args[10];
lean_object* v___y_2613_ = _args[11];
lean_object* v___y_2614_ = _args[12];
lean_object* v___y_2615_ = _args[13];
lean_object* v___y_2616_ = _args[14];
lean_object* v___y_2617_ = _args[15];
lean_object* v___y_2618_ = _args[16];
_start:
{
uint8_t v_a_19085__boxed_2619_; lean_object* v_res_2620_; 
v_a_19085__boxed_2619_ = lean_unbox(v_a_2606_);
v_res_2620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2602_, v_fst_2603_, v_struct_2604_, v_structName_2605_, v_a_19085__boxed_2619_, v___f_2607_, v_snd_2608_, v_____r_2609_, v_ctorType_2610_, v_j_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec(v_j_2611_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2621_, lean_object* v_struct_2622_, lean_object* v_structName_2623_, uint8_t v_a_2624_, lean_object* v_idx_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_b_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___y_2637_; uint8_t v___x_2659_; 
v___x_2659_ = lean_nat_dec_le(v_a_2627_, v_upperBound_2621_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_idx_2625_);
lean_dec(v_structName_2623_);
lean_dec_ref(v_struct_2622_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_b_2628_);
return v___x_2660_;
}
else
{
lean_object* v_snd_2661_; lean_object* v_snd_2662_; lean_object* v_fst_2663_; lean_object* v_fst_2664_; lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___f_2667_; uint8_t v___x_2668_; 
v_snd_2661_ = lean_ctor_get(v_b_2628_, 1);
lean_inc(v_snd_2661_);
v_snd_2662_ = lean_ctor_get(v_snd_2661_, 1);
lean_inc(v_snd_2662_);
v_fst_2663_ = lean_ctor_get(v_b_2628_, 0);
lean_inc(v_fst_2663_);
lean_dec_ref(v_b_2628_);
v_fst_2664_ = lean_ctor_get(v_snd_2661_, 0);
lean_inc(v_fst_2664_);
lean_dec(v_snd_2661_);
v_fst_2665_ = lean_ctor_get(v_snd_2662_, 0);
lean_inc(v_fst_2665_);
v_snd_2666_ = lean_ctor_get(v_snd_2662_, 1);
lean_inc(v_snd_2666_);
lean_dec(v_snd_2662_);
lean_inc_ref(v_a_2626_);
lean_inc(v_idx_2625_);
lean_inc(v_structName_2623_);
lean_inc_ref(v_struct_2622_);
v___f_2667_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2667_, 0, v_struct_2622_);
lean_closure_set(v___f_2667_, 1, v_structName_2623_);
lean_closure_set(v___f_2667_, 2, v_idx_2625_);
lean_closure_set(v___f_2667_, 3, v_a_2626_);
v___x_2668_ = l_Lean_Expr_isForall(v_fst_2663_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_expr_instantiate_rev_range(v_fst_2663_, v_fst_2665_, v_a_2627_, v_fst_2664_);
lean_dec(v_fst_2665_);
lean_dec(v_fst_2663_);
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
v___x_2670_ = lean_whnf(v___x_2669_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_box(0);
lean_inc(v_structName_2623_);
lean_inc_ref(v_struct_2622_);
lean_inc(v_a_2627_);
v___x_2673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2627_, v_fst_2664_, v_struct_2622_, v_structName_2623_, v_a_2624_, v___f_2667_, v_snd_2666_, v___x_2672_, v_a_2671_, v_a_2627_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
v___y_2637_ = v___x_2673_;
goto v___jp_2636_;
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec_ref(v___f_2667_);
lean_dec(v_snd_2666_);
lean_dec(v_fst_2664_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_idx_2625_);
lean_dec(v_structName_2623_);
lean_dec_ref(v_struct_2622_);
v_a_2674_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2670_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2670_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_box(0);
lean_inc(v_structName_2623_);
lean_inc_ref(v_struct_2622_);
lean_inc(v_a_2627_);
v___x_2683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2627_, v_fst_2664_, v_struct_2622_, v_structName_2623_, v_a_2624_, v___f_2667_, v_snd_2666_, v___x_2682_, v_fst_2663_, v_fst_2665_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v_fst_2665_);
v___y_2637_ = v___x_2683_;
goto v___jp_2636_;
}
}
v___jp_2636_:
{
if (lean_obj_tag(v___y_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2650_; 
v_a_2638_ = lean_ctor_get(v___y_2637_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___y_2637_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2640_ = v___y_2637_;
v_isShared_2641_ = v_isSharedCheck_2650_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___y_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2650_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
if (lean_obj_tag(v_a_2638_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; 
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_idx_2625_);
lean_dec(v_structName_2623_);
lean_dec_ref(v_struct_2622_);
v_a_2642_ = lean_ctor_get(v_a_2638_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v_a_2638_, 1);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v_a_2642_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_del_object(v___x_2640_);
v_a_2646_ = lean_ctor_get(v_a_2638_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v_a_2638_, 1);
v___x_2647_ = lean_unsigned_to_nat(1u);
v___x_2648_ = lean_nat_add(v_a_2627_, v___x_2647_);
lean_dec(v_a_2627_);
v_a_2627_ = v___x_2648_;
v_b_2628_ = v_a_2646_;
goto _start;
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_idx_2625_);
lean_dec(v_structName_2623_);
lean_dec_ref(v_struct_2622_);
v_a_2651_ = lean_ctor_get(v___y_2637_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___y_2637_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___y_2637_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___y_2637_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2684_, lean_object* v_struct_2685_, lean_object* v_structName_2686_, lean_object* v_a_2687_, lean_object* v_idx_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v_a_19242__boxed_2699_; lean_object* v_res_2700_; 
v_a_19242__boxed_2699_ = lean_unbox(v_a_2687_);
v_res_2700_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2684_, v_struct_2685_, v_structName_2686_, v_a_19242__boxed_2699_, v_idx_2688_, v_a_2689_, v_a_2690_, v_b_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec(v_upperBound_2684_);
return v_res_2700_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2703_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2704_ = lean_unsigned_to_nat(18u);
v___x_2705_ = lean_unsigned_to_nat(1962u);
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2708_ = l_mkPanicMessageWithDecl(v___x_2707_, v___x_2706_, v___x_2705_, v___x_2704_, v___x_2703_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2715_; lean_object* v_dummy_2716_; 
v___x_2715_ = lean_box(0);
v_dummy_2716_ = l_Lean_Expr_sort___override(v___x_2715_);
return v_dummy_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2717_, lean_object* v_structName_2718_, lean_object* v_idx_2719_, lean_object* v_struct_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2735_; uint8_t v___x_2739_; 
v___x_2739_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2721_);
if (v___x_2739_ == 0)
{
lean_dec(v_idx_2719_);
lean_dec(v_structName_2718_);
if (lean_obj_tag(v_e_2717_) == 11)
{
lean_object* v_expr_2740_; lean_object* v_typeName_2741_; lean_object* v_idx_2742_; lean_object* v_struct_2743_; size_t v___x_2744_; size_t v___x_2745_; uint8_t v___x_2746_; 
v_expr_2740_ = lean_ctor_get(v_struct_2720_, 0);
lean_inc_ref(v_expr_2740_);
lean_dec_ref(v_struct_2720_);
v_typeName_2741_ = lean_ctor_get(v_e_2717_, 0);
v_idx_2742_ = lean_ctor_get(v_e_2717_, 1);
v_struct_2743_ = lean_ctor_get(v_e_2717_, 2);
v___x_2744_ = lean_ptr_addr(v_struct_2743_);
v___x_2745_ = lean_ptr_addr(v_expr_2740_);
v___x_2746_ = lean_usize_dec_eq(v___x_2744_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; 
lean_inc(v_idx_2742_);
lean_inc(v_typeName_2741_);
lean_dec_ref_known(v_e_2717_, 3);
v___x_2747_ = l_Lean_Expr_proj___override(v_typeName_2741_, v_idx_2742_, v_expr_2740_);
v___y_2735_ = v___x_2747_;
goto v___jp_2734_;
}
else
{
lean_dec_ref(v_expr_2740_);
v___y_2735_ = v_e_2717_;
goto v___jp_2734_;
}
}
else
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec_ref(v_struct_2720_);
lean_dec_ref(v_e_2717_);
v___x_2748_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2749_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2748_);
v___y_2735_ = v___x_2749_;
goto v___jp_2734_;
}
}
else
{
lean_object* v___x_2750_; 
lean_inc_ref(v_struct_2720_);
v___x_2750_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2720_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
lean_inc(v_a_2726_);
lean_inc_ref(v_a_2725_);
lean_inc(v_a_2724_);
lean_inc_ref(v_a_2723_);
v___x_2752_ = lean_whnf(v_a_2751_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_n(v_a_2753_, 2);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = l_Lean_Meta_isProp(v_a_2753_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2756_ = l_Lean_Expr_getAppFn(v_a_2753_);
if (lean_obj_tag(v___x_2756_) == 4)
{
lean_object* v_declName_2757_; lean_object* v_us_2758_; lean_object* v___x_2759_; lean_object* v_env_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; 
v_declName_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_declName_2757_);
v_us_2758_ = lean_ctor_get(v___x_2756_, 1);
lean_inc(v_us_2758_);
lean_dec_ref_known(v___x_2756_, 2);
v___x_2759_ = lean_st_ref_get(v_a_2726_);
v_env_2763_ = lean_ctor_get(v___x_2759_, 0);
lean_inc_ref(v_env_2763_);
lean_dec(v___x_2759_);
v___x_2764_ = 0;
v___x_2765_ = l_Lean_Environment_find_x3f(v_env_2763_, v_declName_2757_, v___x_2764_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
v___x_2766_ = lean_box(0);
v___x_2767_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2720_, v_structName_2718_, v_idx_2719_, v_a_2753_, lean_box(0), v___x_2766_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2767_;
}
else
{
lean_object* v_val_2768_; 
v_val_2768_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_val_2768_);
lean_dec_ref_known(v___x_2765_, 1);
if (lean_obj_tag(v_val_2768_) == 5)
{
lean_object* v_val_2769_; lean_object* v_ctors_2770_; 
v_val_2769_ = lean_ctor_get(v_val_2768_, 0);
lean_inc_ref(v_val_2769_);
lean_dec_ref_known(v_val_2768_, 1);
v_ctors_2770_ = lean_ctor_get(v_val_2769_, 4);
lean_inc(v_ctors_2770_);
if (lean_obj_tag(v_ctors_2770_) == 1)
{
lean_object* v_tail_2771_; 
v_tail_2771_ = lean_ctor_get(v_ctors_2770_, 1);
if (lean_obj_tag(v_tail_2771_) == 0)
{
lean_object* v_toConstantVal_2772_; lean_object* v_numParams_2773_; lean_object* v_numIndices_2774_; lean_object* v_head_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2884_; 
v_toConstantVal_2772_ = lean_ctor_get(v_val_2769_, 0);
lean_inc_ref(v_toConstantVal_2772_);
v_numParams_2773_ = lean_ctor_get(v_val_2769_, 1);
lean_inc(v_numParams_2773_);
v_numIndices_2774_ = lean_ctor_get(v_val_2769_, 2);
lean_inc(v_numIndices_2774_);
lean_dec_ref(v_val_2769_);
v_head_2775_ = lean_ctor_get(v_ctors_2770_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_ctors_2770_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v_ctors_2770_, 1);
lean_dec(v_unused_2885_);
v___x_2777_ = v_ctors_2770_;
v_isShared_2778_ = v_isSharedCheck_2884_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_head_2775_);
lean_dec(v_ctors_2770_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2884_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2775_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
if (lean_obj_tag(v_a_2780_) == 6)
{
lean_object* v_val_2781_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_name_2862_; uint8_t v___x_2863_; 
v_val_2781_ = lean_ctor_get(v_a_2780_, 0);
lean_inc_ref(v_val_2781_);
lean_dec_ref_known(v_a_2780_, 1);
v_name_2862_ = lean_ctor_get(v_toConstantVal_2772_, 0);
lean_inc(v_name_2862_);
lean_dec_ref(v_toConstantVal_2772_);
v___x_2863_ = lean_name_eq(v_name_2862_, v_structName_2718_);
lean_dec(v_name_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v_val_2781_);
lean_del_object(v___x_2777_);
lean_dec(v_numIndices_2774_);
lean_dec(v_numParams_2773_);
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
v___x_2864_ = lean_box(0);
v___x_2865_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2720_, v_structName_2718_, v_idx_2719_, v_a_2753_, lean_box(0), v___x_2864_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
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
else
{
v___y_2837_ = v_a_2721_;
v___y_2838_ = v_a_2722_;
v___y_2839_ = v_a_2723_;
v___y_2840_ = v_a_2724_;
v___y_2841_ = v_a_2725_;
v___y_2842_ = v_a_2726_;
goto v___jp_2836_;
}
v___jp_2782_:
{
lean_object* v_toConstantVal_2790_; lean_object* v_name_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_toConstantVal_2790_ = lean_ctor_get(v_val_2781_, 0);
lean_inc_ref(v_toConstantVal_2790_);
lean_dec_ref(v_val_2781_);
v_name_2791_ = lean_ctor_get(v_toConstantVal_2790_, 0);
lean_inc(v_name_2791_);
lean_dec_ref(v_toConstantVal_2790_);
v___x_2792_ = l_Lean_mkConst(v_name_2791_, v_us_2758_);
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = l_Array_toSubarray___redArg(v___y_2783_, v___x_2793_, v_numParams_2773_);
v___x_2795_ = l_Subarray_copy___redArg(v___x_2794_);
v___x_2796_ = l_Lean_mkAppN(v___x_2792_, v___x_2795_);
lean_dec_ref(v___x_2795_);
lean_inc(v___y_2789_);
lean_inc_ref(v___y_2788_);
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
v___x_2797_ = lean_infer_type(v___x_2796_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 0);
lean_ctor_set(v___x_2777_, 1, v___x_2799_);
lean_ctor_set(v___x_2777_, 0, v_a_2798_);
v___x_2801_ = v___x_2777_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2798_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
uint8_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_unbox(v_a_2755_);
lean_dec(v_a_2755_);
lean_inc_ref(v_struct_2720_);
lean_inc(v_idx_2719_);
v___x_2803_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2719_, v_struct_2720_, v_structName_2718_, v___x_2802_, v_idx_2719_, v_a_2753_, v___x_2793_, v___x_2801_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v_idx_2719_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v_snd_2805_; lean_object* v_snd_2806_; lean_object* v_snd_2807_; lean_object* v_expr_2808_; lean_object* v___x_2809_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v_snd_2805_ = lean_ctor_get(v_a_2804_, 1);
lean_inc(v_snd_2805_);
lean_dec(v_a_2804_);
v_snd_2806_ = lean_ctor_get(v_snd_2805_, 1);
lean_inc(v_snd_2806_);
lean_dec(v_snd_2805_);
v_snd_2807_ = lean_ctor_get(v_snd_2806_, 1);
lean_inc(v_snd_2807_);
lean_dec(v_snd_2806_);
v_expr_2808_ = lean_ctor_get(v_struct_2720_, 0);
lean_inc_ref(v_expr_2808_);
lean_dec_ref(v_struct_2720_);
v___x_2809_ = l_Lean_Expr_cleanupAnnotations(v_snd_2807_);
lean_dec(v_snd_2807_);
if (lean_obj_tag(v_e_2717_) == 11)
{
lean_object* v_typeName_2810_; lean_object* v_idx_2811_; lean_object* v_struct_2812_; size_t v___x_2813_; size_t v___x_2814_; uint8_t v___x_2815_; 
v_typeName_2810_ = lean_ctor_get(v_e_2717_, 0);
v_idx_2811_ = lean_ctor_get(v_e_2717_, 1);
v_struct_2812_ = lean_ctor_get(v_e_2717_, 2);
v___x_2813_ = lean_ptr_addr(v_struct_2812_);
v___x_2814_ = lean_ptr_addr(v_expr_2808_);
v___x_2815_ = lean_usize_dec_eq(v___x_2813_, v___x_2814_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
lean_inc(v_idx_2811_);
lean_inc(v_typeName_2810_);
lean_dec_ref_known(v_e_2717_, 3);
v___x_2816_ = l_Lean_Expr_proj___override(v_typeName_2810_, v_idx_2811_, v_expr_2808_);
v___y_2729_ = v___x_2809_;
v___y_2730_ = v___x_2816_;
goto v___jp_2728_;
}
else
{
lean_dec_ref(v_expr_2808_);
v___y_2729_ = v___x_2809_;
v___y_2730_ = v_e_2717_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_expr_2808_);
lean_dec_ref(v_e_2717_);
v___x_2817_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2818_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2817_);
v___y_2729_ = v___x_2809_;
v___y_2730_ = v___x_2818_;
goto v___jp_2728_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v_struct_2720_);
lean_dec_ref(v_e_2717_);
v_a_2819_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2803_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2803_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2777_);
lean_dec(v_a_2755_);
lean_dec(v_a_2753_);
lean_dec_ref(v_struct_2720_);
lean_dec(v_idx_2719_);
lean_dec(v_structName_2718_);
lean_dec_ref(v_e_2717_);
v_a_2828_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2797_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2797_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
v___jp_2836_:
{
lean_object* v_dummy_2843_; lean_object* v_nargs_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_dummy_2843_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2844_ = l_Lean_Expr_getAppNumArgs(v_a_2753_);
lean_inc(v_nargs_2844_);
v___x_2845_ = lean_mk_array(v_nargs_2844_, v_dummy_2843_);
v___x_2846_ = lean_unsigned_to_nat(1u);
v___x_2847_ = lean_nat_sub(v_nargs_2844_, v___x_2846_);
lean_dec(v_nargs_2844_);
lean_inc(v_a_2753_);
v___x_2848_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2753_, v___x_2845_, v___x_2847_);
v___x_2849_ = lean_nat_add(v_numParams_2773_, v_numIndices_2774_);
lean_dec(v_numIndices_2774_);
v___x_2850_ = lean_array_get_size(v___x_2848_);
v___x_2851_ = lean_nat_dec_eq(v___x_2849_, v___x_2850_);
lean_dec(v___x_2849_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v___x_2848_);
lean_dec_ref(v_val_2781_);
lean_del_object(v___x_2777_);
lean_dec(v_numParams_2773_);
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
v___x_2852_ = lean_box(0);
v___x_2853_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2720_, v_structName_2718_, v_idx_2719_, v_a_2753_, lean_box(0), v___x_2852_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
v___y_2783_ = v___x_2848_;
v___y_2784_ = v___y_2837_;
v___y_2785_ = v___y_2838_;
v___y_2786_ = v___y_2839_;
v___y_2787_ = v___y_2840_;
v___y_2788_ = v___y_2841_;
v___y_2789_ = v___y_2842_;
goto v___jp_2782_;
}
}
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_dec(v_a_2780_);
lean_del_object(v___x_2777_);
lean_dec(v_numIndices_2774_);
lean_dec(v_numParams_2773_);
lean_dec_ref(v_toConstantVal_2772_);
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
v___x_2874_ = lean_box(0);
v___x_2875_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2720_, v_structName_2718_, v_idx_2719_, v_a_2753_, lean_box(0), v___x_2874_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2875_;
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_del_object(v___x_2777_);
lean_dec(v_numIndices_2774_);
lean_dec(v_numParams_2773_);
lean_dec_ref(v_toConstantVal_2772_);
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec(v_a_2753_);
lean_dec_ref(v_struct_2720_);
lean_dec(v_idx_2719_);
lean_dec(v_structName_2718_);
lean_dec_ref(v_e_2717_);
v_a_2876_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2779_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2779_);
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
}
else
{
lean_dec_ref_known(v_ctors_2770_, 2);
lean_dec_ref(v_val_2769_);
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
goto v___jp_2760_;
}
}
else
{
lean_dec(v_ctors_2770_);
lean_dec_ref(v_val_2769_);
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
goto v___jp_2760_;
}
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec(v_val_2768_);
lean_dec(v_us_2758_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
v___x_2886_ = lean_box(0);
v___x_2887_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2720_, v_structName_2718_, v_idx_2719_, v_a_2753_, lean_box(0), v___x_2886_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2887_;
}
}
v___jp_2760_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_box(0);
v___x_2762_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2720_, v_structName_2718_, v_idx_2719_, v_a_2753_, lean_box(0), v___x_2761_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2762_;
}
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec_ref(v___x_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_e_2717_);
v___x_2888_ = lean_box(0);
v___x_2889_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2720_, v_structName_2718_, v_idx_2719_, v_a_2753_, lean_box(0), v___x_2888_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2889_;
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_a_2753_);
lean_dec_ref(v_struct_2720_);
lean_dec(v_idx_2719_);
lean_dec(v_structName_2718_);
lean_dec_ref(v_e_2717_);
v_a_2890_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2754_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2754_);
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
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v_struct_2720_);
lean_dec(v_idx_2719_);
lean_dec(v_structName_2718_);
lean_dec_ref(v_e_2717_);
v_a_2898_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2752_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2752_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v_struct_2720_);
lean_dec(v_idx_2719_);
lean_dec(v_structName_2718_);
lean_dec_ref(v_e_2717_);
v_a_2906_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2750_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2750_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
v___jp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___y_2729_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___y_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
v___jp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___y_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2914_, lean_object* v_structName_2915_, lean_object* v_idx_2916_, lean_object* v_struct_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2914_, v_structName_2915_, v_idx_2916_, v_struct_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec(v_a_2918_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2926_, lean_object* v_struct_2927_, lean_object* v_structName_2928_, uint8_t v_a_2929_, lean_object* v_idx_2930_, lean_object* v_a_2931_, lean_object* v_inst_2932_, lean_object* v_R_2933_, lean_object* v_a_2934_, lean_object* v_b_2935_, lean_object* v_c_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2926_, v_struct_2927_, v_structName_2928_, v_a_2929_, v_idx_2930_, v_a_2931_, v_a_2934_, v_b_2935_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2945_ = _args[0];
lean_object* v_struct_2946_ = _args[1];
lean_object* v_structName_2947_ = _args[2];
lean_object* v_a_2948_ = _args[3];
lean_object* v_idx_2949_ = _args[4];
lean_object* v_a_2950_ = _args[5];
lean_object* v_inst_2951_ = _args[6];
lean_object* v_R_2952_ = _args[7];
lean_object* v_a_2953_ = _args[8];
lean_object* v_b_2954_ = _args[9];
lean_object* v_c_2955_ = _args[10];
lean_object* v___y_2956_ = _args[11];
lean_object* v___y_2957_ = _args[12];
lean_object* v___y_2958_ = _args[13];
lean_object* v___y_2959_ = _args[14];
lean_object* v___y_2960_ = _args[15];
lean_object* v___y_2961_ = _args[16];
lean_object* v___y_2962_ = _args[17];
_start:
{
uint8_t v_a_19766__boxed_2963_; lean_object* v_res_2964_; 
v_a_19766__boxed_2963_ = lean_unbox(v_a_2948_);
v_res_2964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2945_, v_struct_2946_, v_structName_2947_, v_a_19766__boxed_2963_, v_idx_2949_, v_a_2950_, v_inst_2951_, v_R_2952_, v_a_2953_, v_b_2954_, v_c_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec(v_upperBound_2945_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2965_, size_t v_i_2966_, size_t v_stop_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_usize_dec_eq(v_i_2966_, v_stop_2967_);
if (v___x_2975_ == 0)
{
size_t v___x_2976_; size_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2976_ = ((size_t)1ULL);
v___x_2977_ = lean_usize_sub(v_i_2966_, v___x_2976_);
v___x_2978_ = lean_array_uget_borrowed(v_as_2965_, v___x_2977_);
lean_inc(v___x_2978_);
v___x_2979_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2978_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = l_Lean_Expr_sortLevel_x21(v_a_2980_);
lean_dec(v_a_2980_);
v___x_2982_ = l_Lean_mkLevelIMax_x27(v___x_2981_, v_b_2968_);
v_i_2966_ = v___x_2977_;
v_b_2968_ = v___x_2982_;
goto _start;
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_b_2968_);
v_a_2984_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2979_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2979_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_b_2968_);
return v___x_2992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_2993_, lean_object* v_i_2994_, lean_object* v_stop_2995_, lean_object* v_b_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
size_t v_i_boxed_3003_; size_t v_stop_boxed_3004_; lean_object* v_res_3005_; 
v_i_boxed_3003_ = lean_unbox_usize(v_i_2994_);
lean_dec(v_i_2994_);
v_stop_boxed_3004_ = lean_unbox_usize(v_stop_2995_);
lean_dec(v_stop_2995_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_2993_, v_i_boxed_3003_, v_stop_boxed_3004_, v_b_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v_as_2993_);
return v_res_3005_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_3010_ = lean_unsigned_to_nat(14u);
v___x_3011_ = lean_unsigned_to_nat(22u);
v___x_3012_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_3013_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_3014_ = l_mkPanicMessageWithDecl(v___x_3013_, v___x_3012_, v___x_3011_, v___x_3010_, v___x_3009_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_3015_, lean_object* v_doms_3016_, lean_object* v_body_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_lctx_3025_; lean_object* v_expr_3026_; uint8_t v___x_3027_; uint8_t v___x_3028_; lean_object* v___x_3029_; lean_object* v_a_3031_; uint8_t v___x_3036_; 
v_lctx_3025_ = lean_ctor_get(v_a_3020_, 2);
v_expr_3026_ = lean_ctor_get(v_body_3017_, 0);
v___x_3027_ = 1;
v___x_3028_ = 0;
lean_inc_ref(v_lctx_3025_);
v___x_3029_ = l_Lean_LocalContext_mkForall(v_lctx_3025_, v_fvars_3015_, v_expr_3026_, v___x_3027_, v___x_3028_);
v___x_3036_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3018_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3045_; 
v_isSharedCheck_3045_ = !lean_is_exclusive(v_body_3017_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; lean_object* v_unused_3047_; 
v_unused_3046_ = lean_ctor_get(v_body_3017_, 1);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_body_3017_, 0);
lean_dec(v_unused_3047_);
v___x_3038_ = v_body_3017_;
v_isShared_3039_ = v_isSharedCheck_3045_;
goto v_resetjp_3037_;
}
else
{
lean_dec(v_body_3017_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3045_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3040_ = lean_box(0);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v___x_3040_);
lean_ctor_set(v___x_3038_, 0, v___x_3029_);
v___x_3042_ = v___x_3038_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
}
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___y_3051_; lean_object* v_type_x3f_3068_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v_type_x3f_3068_ = lean_ctor_get(v_a_3049_, 1);
lean_inc(v_type_x3f_3068_);
lean_dec(v_a_3049_);
if (lean_obj_tag(v_type_x3f_3068_) == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3070_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3069_);
v___y_3051_ = v___x_3070_;
goto v___jp_3050_;
}
else
{
lean_object* v_val_3071_; 
v_val_3071_ = lean_ctor_get(v_type_x3f_3068_, 0);
lean_inc(v_val_3071_);
lean_dec_ref_known(v_type_x3f_3068_, 1);
v___y_3051_ = v_val_3071_;
goto v___jp_3050_;
}
v___jp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3052_ = l_Lean_Expr_sortLevel_x21(v___y_3051_);
lean_dec_ref(v___y_3051_);
v___x_3053_ = lean_array_get_size(v_doms_3016_);
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = lean_nat_dec_lt(v___x_3054_, v___x_3053_);
if (v___x_3055_ == 0)
{
v_a_3031_ = v___x_3052_;
goto v___jp_3030_;
}
else
{
size_t v___x_3056_; size_t v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = lean_usize_of_nat(v___x_3053_);
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_3016_, v___x_3056_, v___x_3057_, v___x_3052_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v_a_3031_ = v_a_3059_;
goto v___jp_3030_;
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v___x_3029_);
v_a_3060_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3058_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3058_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3029_);
return v___x_3048_;
}
}
v___jp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3032_ = l_Lean_Expr_sort___override(v_a_3031_);
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3029_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3072_, lean_object* v_doms_3073_, lean_object* v_body_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3072_, v_doms_3073_, v_body_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_doms_3073_);
lean_dec_ref(v_fvars_3072_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3083_, size_t v_i_3084_, size_t v_stop_3085_, lean_object* v_b_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3083_, v_i_3084_, v_stop_3085_, v_b_3086_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3095_, lean_object* v_i_3096_, lean_object* v_stop_3097_, lean_object* v_b_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
size_t v_i_boxed_3106_; size_t v_stop_boxed_3107_; lean_object* v_res_3108_; 
v_i_boxed_3106_ = lean_unbox_usize(v_i_3096_);
lean_dec(v_i_3096_);
v_stop_boxed_3107_ = lean_unbox_usize(v_stop_3097_);
lean_dec(v_stop_3097_);
v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3095_, v_i_boxed_3106_, v_stop_boxed_3107_, v_b_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v_as_3095_);
return v_res_3108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3109_, lean_object* v_opt_3110_){
_start:
{
lean_object* v_name_3111_; lean_object* v_defValue_3112_; lean_object* v_map_3113_; lean_object* v___x_3114_; 
v_name_3111_ = lean_ctor_get(v_opt_3110_, 0);
v_defValue_3112_ = lean_ctor_get(v_opt_3110_, 1);
v_map_3113_ = lean_ctor_get(v_opts_3109_, 0);
v___x_3114_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3113_, v_name_3111_);
if (lean_obj_tag(v___x_3114_) == 0)
{
uint8_t v___x_3115_; 
v___x_3115_ = lean_unbox(v_defValue_3112_);
return v___x_3115_;
}
else
{
lean_object* v_val_3116_; 
v_val_3116_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v___x_3114_, 1);
if (lean_obj_tag(v_val_3116_) == 1)
{
uint8_t v_v_3117_; 
v_v_3117_ = lean_ctor_get_uint8(v_val_3116_, 0);
lean_dec_ref_known(v_val_3116_, 0);
return v_v_3117_;
}
else
{
uint8_t v___x_3118_; 
lean_dec(v_val_3116_);
v___x_3118_ = lean_unbox(v_defValue_3112_);
return v___x_3118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3119_, lean_object* v_opt_3120_){
_start:
{
uint8_t v_res_3121_; lean_object* v_r_3122_; 
v_res_3121_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3119_, v_opt_3120_);
lean_dec_ref(v_opt_3120_);
lean_dec_ref(v_opts_3119_);
v_r_3122_ = lean_box(v_res_3121_);
return v_r_3122_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3123_){
_start:
{
if (lean_obj_tag(v_x_3123_) == 0)
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
v_a_3125_ = lean_ctor_get(v_x_3123_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_x_3123_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v_x_3123_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v_x_3123_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set_tag(v___x_3127_, 1);
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3133_ = lean_ctor_get(v_x_3123_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_x_3123_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v_x_3123_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v_x_3123_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 0);
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3144_){
_start:
{
if (lean_obj_tag(v_e_3144_) == 0)
{
uint8_t v___x_3145_; 
v___x_3145_ = 2;
return v___x_3145_;
}
else
{
uint8_t v___x_3146_; 
v___x_3146_ = 0;
return v___x_3146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3147_){
_start:
{
uint8_t v_res_3148_; lean_object* v_r_3149_; 
v_res_3148_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3147_);
lean_dec_ref(v_e_3147_);
v_r_3149_ = lean_box(v_res_3148_);
return v_r_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3150_, lean_object* v_opt_3151_){
_start:
{
lean_object* v_name_3152_; lean_object* v_defValue_3153_; lean_object* v_map_3154_; lean_object* v___x_3155_; 
v_name_3152_ = lean_ctor_get(v_opt_3151_, 0);
v_defValue_3153_ = lean_ctor_get(v_opt_3151_, 1);
v_map_3154_ = lean_ctor_get(v_opts_3150_, 0);
v___x_3155_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3154_, v_name_3152_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_inc(v_defValue_3153_);
return v_defValue_3153_;
}
else
{
lean_object* v_val_3156_; 
v_val_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_val_3156_);
lean_dec_ref_known(v___x_3155_, 1);
if (lean_obj_tag(v_val_3156_) == 3)
{
lean_object* v_v_3157_; 
v_v_3157_ = lean_ctor_get(v_val_3156_, 0);
lean_inc(v_v_3157_);
lean_dec_ref_known(v_val_3156_, 1);
return v_v_3157_;
}
else
{
lean_dec(v_val_3156_);
lean_inc(v_defValue_3153_);
return v_defValue_3153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3158_, lean_object* v_opt_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3158_, v_opt_3159_);
lean_dec_ref(v_opt_3159_);
lean_dec_ref(v_opts_3158_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3161_, size_t v_i_3162_, lean_object* v_bs_3163_){
_start:
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_usize_dec_lt(v_i_3162_, v_sz_3161_);
if (v___x_3164_ == 0)
{
return v_bs_3163_;
}
else
{
lean_object* v_v_3165_; lean_object* v_msg_3166_; lean_object* v___x_3167_; lean_object* v_bs_x27_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v_v_3165_ = lean_array_uget_borrowed(v_bs_3163_, v_i_3162_);
v_msg_3166_ = lean_ctor_get(v_v_3165_, 1);
lean_inc_ref(v_msg_3166_);
v___x_3167_ = lean_unsigned_to_nat(0u);
v_bs_x27_3168_ = lean_array_uset(v_bs_3163_, v_i_3162_, v___x_3167_);
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = lean_usize_add(v_i_3162_, v___x_3169_);
v___x_3171_ = lean_array_uset(v_bs_x27_3168_, v_i_3162_, v_msg_3166_);
v_i_3162_ = v___x_3170_;
v_bs_3163_ = v___x_3171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3173_, lean_object* v_i_3174_, lean_object* v_bs_3175_){
_start:
{
size_t v_sz_boxed_3176_; size_t v_i_boxed_3177_; lean_object* v_res_3178_; 
v_sz_boxed_3176_ = lean_unbox_usize(v_sz_3173_);
lean_dec(v_sz_3173_);
v_i_boxed_3177_ = lean_unbox_usize(v_i_3174_);
lean_dec(v_i_3174_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3176_, v_i_boxed_3177_, v_bs_3175_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3179_, lean_object* v_data_3180_, lean_object* v_ref_3181_, lean_object* v_msg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_toCold_3188_; lean_object* v_currRecDepth_3189_; lean_object* v_ref_3190_; uint16_t v_optionFlags_3191_; uint8_t v_suppressElabErrors_3192_; uint8_t v_checkDeprecated_3193_; uint8_t v_isRecordingDeps_3194_; lean_object* v_ref_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_traceState_3198_; lean_object* v_traces_3199_; lean_object* v___x_3200_; size_t v_sz_3201_; size_t v___x_3202_; lean_object* v___x_3203_; lean_object* v_msg_3204_; lean_object* v___x_3205_; lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3244_; 
v_toCold_3188_ = lean_ctor_get(v___y_3185_, 0);
v_currRecDepth_3189_ = lean_ctor_get(v___y_3185_, 1);
v_ref_3190_ = lean_ctor_get(v___y_3185_, 2);
v_optionFlags_3191_ = lean_ctor_get_uint16(v___y_3185_, sizeof(void*)*3);
v_suppressElabErrors_3192_ = lean_ctor_get_uint8(v___y_3185_, sizeof(void*)*3 + 2);
v_checkDeprecated_3193_ = lean_ctor_get_uint8(v___y_3185_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3194_ = lean_ctor_get_uint8(v___y_3185_, sizeof(void*)*3 + 4);
v_ref_3195_ = l_Lean_replaceRef(v_ref_3181_, v_ref_3190_);
lean_inc(v_currRecDepth_3189_);
lean_inc_ref(v_toCold_3188_);
v___x_3196_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3196_, 0, v_toCold_3188_);
lean_ctor_set(v___x_3196_, 1, v_currRecDepth_3189_);
lean_ctor_set(v___x_3196_, 2, v_ref_3195_);
lean_ctor_set_uint16(v___x_3196_, sizeof(void*)*3, v_optionFlags_3191_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*3 + 2, v_suppressElabErrors_3192_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*3 + 3, v_checkDeprecated_3193_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*3 + 4, v_isRecordingDeps_3194_);
v___x_3197_ = lean_st_ref_get(v___y_3186_);
v_traceState_3198_ = lean_ctor_get(v___x_3197_, 4);
lean_inc_ref(v_traceState_3198_);
lean_dec(v___x_3197_);
v_traces_3199_ = lean_ctor_get(v_traceState_3198_, 0);
lean_inc_ref(v_traces_3199_);
lean_dec_ref(v_traceState_3198_);
v___x_3200_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3199_);
lean_dec_ref(v_traces_3199_);
v_sz_3201_ = lean_array_size(v___x_3200_);
v___x_3202_ = ((size_t)0ULL);
v___x_3203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3201_, v___x_3202_, v___x_3200_);
v_msg_3204_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3204_, 0, v_data_3180_);
lean_ctor_set(v_msg_3204_, 1, v_msg_3182_);
lean_ctor_set(v_msg_3204_, 2, v___x_3203_);
v___x_3205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3204_, v___y_3183_, v___y_3184_, v___x_3196_, v___y_3186_);
lean_dec_ref_known(v___x_3196_, 3);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3244_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3244_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v_traceState_3211_; lean_object* v_env_3212_; lean_object* v_nextMacroScope_3213_; lean_object* v_ngen_3214_; lean_object* v_auxDeclNGen_3215_; lean_object* v_cache_3216_; lean_object* v_recordedDeps_3217_; lean_object* v_messages_3218_; lean_object* v_infoState_3219_; lean_object* v_snapshotTasks_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3243_; 
v___x_3210_ = lean_st_ref_take(v___y_3186_);
v_traceState_3211_ = lean_ctor_get(v___x_3210_, 4);
v_env_3212_ = lean_ctor_get(v___x_3210_, 0);
v_nextMacroScope_3213_ = lean_ctor_get(v___x_3210_, 1);
v_ngen_3214_ = lean_ctor_get(v___x_3210_, 2);
v_auxDeclNGen_3215_ = lean_ctor_get(v___x_3210_, 3);
v_cache_3216_ = lean_ctor_get(v___x_3210_, 5);
v_recordedDeps_3217_ = lean_ctor_get(v___x_3210_, 6);
v_messages_3218_ = lean_ctor_get(v___x_3210_, 7);
v_infoState_3219_ = lean_ctor_get(v___x_3210_, 8);
v_snapshotTasks_3220_ = lean_ctor_get(v___x_3210_, 9);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3222_ = v___x_3210_;
v_isShared_3223_ = v_isSharedCheck_3243_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_snapshotTasks_3220_);
lean_inc(v_infoState_3219_);
lean_inc(v_messages_3218_);
lean_inc(v_recordedDeps_3217_);
lean_inc(v_cache_3216_);
lean_inc(v_traceState_3211_);
lean_inc(v_auxDeclNGen_3215_);
lean_inc(v_ngen_3214_);
lean_inc(v_nextMacroScope_3213_);
lean_inc(v_env_3212_);
lean_dec(v___x_3210_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3243_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
uint64_t v_tid_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3241_; 
v_tid_3224_ = lean_ctor_get_uint64(v_traceState_3211_, sizeof(void*)*1);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_traceState_3211_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v_traceState_3211_, 0);
lean_dec(v_unused_3242_);
v___x_3226_ = v_traceState_3211_;
v_isShared_3227_ = v_isSharedCheck_3241_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v_traceState_3211_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3241_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v_ref_3181_);
lean_ctor_set(v___x_3229_, 1, v_a_3206_);
v___x_3230_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3179_, v___x_3229_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3230_);
v___x_3232_ = v___x_3226_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3230_);
lean_ctor_set_uint64(v_reuseFailAlloc_3240_, sizeof(void*)*1, v_tid_3224_);
v___x_3232_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3234_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 4, v___x_3232_);
v___x_3234_ = v___x_3222_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_env_3212_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_nextMacroScope_3213_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_ngen_3214_);
lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_auxDeclNGen_3215_);
lean_ctor_set(v_reuseFailAlloc_3239_, 4, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3239_, 5, v_cache_3216_);
lean_ctor_set(v_reuseFailAlloc_3239_, 6, v_recordedDeps_3217_);
lean_ctor_set(v_reuseFailAlloc_3239_, 7, v_messages_3218_);
lean_ctor_set(v_reuseFailAlloc_3239_, 8, v_infoState_3219_);
lean_ctor_set(v_reuseFailAlloc_3239_, 9, v_snapshotTasks_3220_);
v___x_3234_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3235_ = lean_st_ref_put(v___y_3186_, v___x_3234_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3228_);
v___x_3237_ = v___x_3208_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3228_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3245_, lean_object* v_data_3246_, lean_object* v_ref_3247_, lean_object* v_msg_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3245_, v_data_3246_, v_ref_3247_, v_msg_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3254_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3257_ = l_Lean_stringToMessageData(v___x_3256_);
return v___x_3257_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3258_; double v___x_3259_; 
v___x_3258_ = lean_unsigned_to_nat(1000u);
v___x_3259_ = lean_float_of_nat(v___x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3260_, uint8_t v_collapsed_3261_, lean_object* v_tag_3262_, lean_object* v_opts_3263_, uint8_t v_clsEnabled_3264_, lean_object* v_oldTraces_3265_, lean_object* v_msg_3266_, lean_object* v_resStartStop_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v_data_3280_; lean_object* v_fst_3291_; lean_object* v_snd_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; lean_object* v___y_3296_; lean_object* v_a_3297_; uint8_t v___y_3312_; double v___y_3344_; 
v_fst_3275_ = lean_ctor_get(v_resStartStop_3267_, 0);
lean_inc(v_fst_3275_);
v_snd_3276_ = lean_ctor_get(v_resStartStop_3267_, 1);
lean_inc(v_snd_3276_);
lean_dec_ref(v_resStartStop_3267_);
v_fst_3291_ = lean_ctor_get(v_snd_3276_, 0);
lean_inc(v_fst_3291_);
v_snd_3292_ = lean_ctor_get(v_snd_3276_, 1);
lean_inc(v_snd_3292_);
lean_dec(v_snd_3276_);
v___x_3293_ = l_Lean_trace_profiler;
v___x_3294_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3263_, v___x_3293_);
if (v___x_3294_ == 0)
{
v___y_3312_ = v___x_3294_;
goto v___jp_3311_;
}
else
{
lean_object* v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3350_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3263_, v___x_3349_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; lean_object* v___x_3352_; double v___x_3353_; double v___x_3354_; double v___x_3355_; 
v___x_3351_ = l_Lean_trace_profiler_threshold;
v___x_3352_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3263_, v___x_3351_);
v___x_3353_ = lean_float_of_nat(v___x_3352_);
v___x_3354_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3355_ = lean_float_div(v___x_3353_, v___x_3354_);
v___y_3344_ = v___x_3355_;
goto v___jp_3343_;
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; double v___x_3358_; 
v___x_3356_ = l_Lean_trace_profiler_threshold;
v___x_3357_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3263_, v___x_3356_);
v___x_3358_ = lean_float_of_nat(v___x_3357_);
v___y_3344_ = v___x_3358_;
goto v___jp_3343_;
}
}
v___jp_3277_:
{
lean_object* v___x_3281_; 
lean_inc(v___y_3279_);
v___x_3281_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3265_, v_data_3280_, v___y_3279_, v___y_3278_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v___x_3282_; 
lean_dec_ref_known(v___x_3281_, 1);
v___x_3282_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3275_);
return v___x_3282_;
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_fst_3275_);
v_a_3283_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3281_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3281_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
v___jp_3295_:
{
uint8_t v_result_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; double v___x_3301_; lean_object* v_data_3302_; 
v_result_3298_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3275_);
v___x_3299_ = lean_box(v_result_3298_);
v___x_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
v___x_3301_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3262_);
lean_inc_ref(v___x_3300_);
lean_inc(v_cls_3260_);
v_data_3302_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3302_, 0, v_cls_3260_);
lean_ctor_set(v_data_3302_, 1, v___x_3300_);
lean_ctor_set(v_data_3302_, 2, v_tag_3262_);
lean_ctor_set_float(v_data_3302_, sizeof(void*)*3, v___x_3301_);
lean_ctor_set_float(v_data_3302_, sizeof(void*)*3 + 8, v___x_3301_);
lean_ctor_set_uint8(v_data_3302_, sizeof(void*)*3 + 16, v_collapsed_3261_);
if (v___x_3294_ == 0)
{
lean_dec_ref_known(v___x_3300_, 1);
lean_dec(v_snd_3292_);
lean_dec(v_fst_3291_);
lean_dec_ref(v_tag_3262_);
lean_dec(v_cls_3260_);
v___y_3278_ = v_a_3297_;
v___y_3279_ = v___y_3296_;
v_data_3280_ = v_data_3302_;
goto v___jp_3277_;
}
else
{
lean_object* v_data_3303_; double v___x_3304_; double v___x_3305_; 
lean_dec_ref_known(v_data_3302_, 3);
v_data_3303_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3303_, 0, v_cls_3260_);
lean_ctor_set(v_data_3303_, 1, v___x_3300_);
lean_ctor_set(v_data_3303_, 2, v_tag_3262_);
v___x_3304_ = lean_unbox_float(v_fst_3291_);
lean_dec(v_fst_3291_);
lean_ctor_set_float(v_data_3303_, sizeof(void*)*3, v___x_3304_);
v___x_3305_ = lean_unbox_float(v_snd_3292_);
lean_dec(v_snd_3292_);
lean_ctor_set_float(v_data_3303_, sizeof(void*)*3 + 8, v___x_3305_);
lean_ctor_set_uint8(v_data_3303_, sizeof(void*)*3 + 16, v_collapsed_3261_);
v___y_3278_ = v_a_3297_;
v___y_3279_ = v___y_3296_;
v_data_3280_ = v_data_3303_;
goto v___jp_3277_;
}
}
v___jp_3306_:
{
lean_object* v_ref_3307_; lean_object* v___x_3308_; 
v_ref_3307_ = lean_ctor_get(v___y_3272_, 2);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc(v___y_3268_);
lean_inc(v_fst_3275_);
v___x_3308_ = lean_apply_8(v_msg_3266_, v_fst_3275_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, lean_box(0));
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v___y_3296_ = v_ref_3307_;
v_a_3297_ = v_a_3309_;
goto v___jp_3295_;
}
else
{
lean_object* v___x_3310_; 
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3296_ = v_ref_3307_;
v_a_3297_ = v___x_3310_;
goto v___jp_3295_;
}
}
v___jp_3311_:
{
if (v_clsEnabled_3264_ == 0)
{
if (v___y_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v_traceState_3314_; lean_object* v_env_3315_; lean_object* v_nextMacroScope_3316_; lean_object* v_ngen_3317_; lean_object* v_auxDeclNGen_3318_; lean_object* v_cache_3319_; lean_object* v_recordedDeps_3320_; lean_object* v_messages_3321_; lean_object* v_infoState_3322_; lean_object* v_snapshotTasks_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_snd_3292_);
lean_dec(v_fst_3291_);
lean_dec_ref(v_msg_3266_);
lean_dec_ref(v_tag_3262_);
lean_dec(v_cls_3260_);
v___x_3313_ = lean_st_ref_take(v___y_3273_);
v_traceState_3314_ = lean_ctor_get(v___x_3313_, 4);
v_env_3315_ = lean_ctor_get(v___x_3313_, 0);
v_nextMacroScope_3316_ = lean_ctor_get(v___x_3313_, 1);
v_ngen_3317_ = lean_ctor_get(v___x_3313_, 2);
v_auxDeclNGen_3318_ = lean_ctor_get(v___x_3313_, 3);
v_cache_3319_ = lean_ctor_get(v___x_3313_, 5);
v_recordedDeps_3320_ = lean_ctor_get(v___x_3313_, 6);
v_messages_3321_ = lean_ctor_get(v___x_3313_, 7);
v_infoState_3322_ = lean_ctor_get(v___x_3313_, 8);
v_snapshotTasks_3323_ = lean_ctor_get(v___x_3313_, 9);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3325_ = v___x_3313_;
v_isShared_3326_ = v_isSharedCheck_3342_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_snapshotTasks_3323_);
lean_inc(v_infoState_3322_);
lean_inc(v_messages_3321_);
lean_inc(v_recordedDeps_3320_);
lean_inc(v_cache_3319_);
lean_inc(v_traceState_3314_);
lean_inc(v_auxDeclNGen_3318_);
lean_inc(v_ngen_3317_);
lean_inc(v_nextMacroScope_3316_);
lean_inc(v_env_3315_);
lean_dec(v___x_3313_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3342_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
uint64_t v_tid_3327_; lean_object* v_traces_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3341_; 
v_tid_3327_ = lean_ctor_get_uint64(v_traceState_3314_, sizeof(void*)*1);
v_traces_3328_ = lean_ctor_get(v_traceState_3314_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_traceState_3314_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3330_ = v_traceState_3314_;
v_isShared_3331_ = v_isSharedCheck_3341_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_traces_3328_);
lean_dec(v_traceState_3314_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3341_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3265_, v_traces_3328_);
lean_dec_ref(v_traces_3328_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3332_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3332_);
lean_ctor_set_uint64(v_reuseFailAlloc_3340_, sizeof(void*)*1, v_tid_3327_);
v___x_3334_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3336_; 
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 4, v___x_3334_);
v___x_3336_ = v___x_3325_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_env_3315_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_nextMacroScope_3316_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_ngen_3317_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_auxDeclNGen_3318_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3339_, 5, v_cache_3319_);
lean_ctor_set(v_reuseFailAlloc_3339_, 6, v_recordedDeps_3320_);
lean_ctor_set(v_reuseFailAlloc_3339_, 7, v_messages_3321_);
lean_ctor_set(v_reuseFailAlloc_3339_, 8, v_infoState_3322_);
lean_ctor_set(v_reuseFailAlloc_3339_, 9, v_snapshotTasks_3323_);
v___x_3336_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = lean_st_ref_put(v___y_3273_, v___x_3336_);
v___x_3338_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3275_);
return v___x_3338_;
}
}
}
}
}
else
{
goto v___jp_3306_;
}
}
else
{
goto v___jp_3306_;
}
}
v___jp_3343_:
{
double v___x_3345_; double v___x_3346_; double v___x_3347_; uint8_t v___x_3348_; 
v___x_3345_ = lean_unbox_float(v_snd_3292_);
v___x_3346_ = lean_unbox_float(v_fst_3291_);
v___x_3347_ = lean_float_sub(v___x_3345_, v___x_3346_);
v___x_3348_ = lean_float_decLt(v___y_3344_, v___x_3347_);
v___y_3312_ = v___x_3348_;
goto v___jp_3311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3359_, lean_object* v_collapsed_3360_, lean_object* v_tag_3361_, lean_object* v_opts_3362_, lean_object* v_clsEnabled_3363_, lean_object* v_oldTraces_3364_, lean_object* v_msg_3365_, lean_object* v_resStartStop_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
uint8_t v_collapsed_boxed_3374_; uint8_t v_clsEnabled_boxed_3375_; lean_object* v_res_3376_; 
v_collapsed_boxed_3374_ = lean_unbox(v_collapsed_3360_);
v_clsEnabled_boxed_3375_ = lean_unbox(v_clsEnabled_3363_);
v_res_3376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3359_, v_collapsed_boxed_3374_, v_tag_3361_, v_opts_3362_, v_clsEnabled_boxed_3375_, v_oldTraces_3364_, v_msg_3365_, v_resStartStop_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v_opts_3362_);
return v_res_3376_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = lean_unsigned_to_nat(32u);
v___x_3378_ = lean_mk_empty_array_with_capacity(v___x_3377_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3380_ = ((size_t)5ULL);
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = lean_unsigned_to_nat(32u);
v___x_3383_ = lean_mk_empty_array_with_capacity(v___x_3382_);
v___x_3384_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3385_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v___x_3383_);
lean_ctor_set(v___x_3385_, 2, v___x_3381_);
lean_ctor_set(v___x_3385_, 3, v___x_3381_);
lean_ctor_set_usize(v___x_3385_, 4, v___x_3380_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3388_; lean_object* v_traceState_3389_; lean_object* v_traces_3390_; lean_object* v___x_3391_; lean_object* v_traceState_3392_; lean_object* v_env_3393_; lean_object* v_nextMacroScope_3394_; lean_object* v_ngen_3395_; lean_object* v_auxDeclNGen_3396_; lean_object* v_cache_3397_; lean_object* v_recordedDeps_3398_; lean_object* v_messages_3399_; lean_object* v_infoState_3400_; lean_object* v_snapshotTasks_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3420_; 
v___x_3388_ = lean_st_ref_get(v___y_3386_);
v_traceState_3389_ = lean_ctor_get(v___x_3388_, 4);
lean_inc_ref(v_traceState_3389_);
lean_dec(v___x_3388_);
v_traces_3390_ = lean_ctor_get(v_traceState_3389_, 0);
lean_inc_ref(v_traces_3390_);
lean_dec_ref(v_traceState_3389_);
v___x_3391_ = lean_st_ref_take(v___y_3386_);
v_traceState_3392_ = lean_ctor_get(v___x_3391_, 4);
v_env_3393_ = lean_ctor_get(v___x_3391_, 0);
v_nextMacroScope_3394_ = lean_ctor_get(v___x_3391_, 1);
v_ngen_3395_ = lean_ctor_get(v___x_3391_, 2);
v_auxDeclNGen_3396_ = lean_ctor_get(v___x_3391_, 3);
v_cache_3397_ = lean_ctor_get(v___x_3391_, 5);
v_recordedDeps_3398_ = lean_ctor_get(v___x_3391_, 6);
v_messages_3399_ = lean_ctor_get(v___x_3391_, 7);
v_infoState_3400_ = lean_ctor_get(v___x_3391_, 8);
v_snapshotTasks_3401_ = lean_ctor_get(v___x_3391_, 9);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3403_ = v___x_3391_;
v_isShared_3404_ = v_isSharedCheck_3420_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_snapshotTasks_3401_);
lean_inc(v_infoState_3400_);
lean_inc(v_messages_3399_);
lean_inc(v_recordedDeps_3398_);
lean_inc(v_cache_3397_);
lean_inc(v_traceState_3392_);
lean_inc(v_auxDeclNGen_3396_);
lean_inc(v_ngen_3395_);
lean_inc(v_nextMacroScope_3394_);
lean_inc(v_env_3393_);
lean_dec(v___x_3391_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3420_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint64_t v_tid_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3418_; 
v_tid_3405_ = lean_ctor_get_uint64(v_traceState_3392_, sizeof(void*)*1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_traceState_3392_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v_traceState_3392_, 0);
lean_dec(v_unused_3419_);
v___x_3407_ = v_traceState_3392_;
v_isShared_3408_ = v_isSharedCheck_3418_;
goto v_resetjp_3406_;
}
else
{
lean_dec(v_traceState_3392_);
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
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_env_3393_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_nextMacroScope_3394_);
lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_ngen_3395_);
lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_auxDeclNGen_3396_);
lean_ctor_set(v_reuseFailAlloc_3416_, 4, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3416_, 5, v_cache_3397_);
lean_ctor_set(v_reuseFailAlloc_3416_, 6, v_recordedDeps_3398_);
lean_ctor_set(v_reuseFailAlloc_3416_, 7, v_messages_3399_);
lean_ctor_set(v_reuseFailAlloc_3416_, 8, v_infoState_3400_);
lean_ctor_set(v_reuseFailAlloc_3416_, 9, v_snapshotTasks_3401_);
v___x_3413_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_st_ref_put(v___y_3386_, v___x_3413_);
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_traces_3390_);
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
lean_object* v___x_3475_; lean_object* v_ngen_3476_; lean_object* v_namePrefix_3477_; lean_object* v_idx_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3508_; 
v___x_3475_ = lean_st_ref_get(v___y_3473_);
v_ngen_3476_ = lean_ctor_get(v___x_3475_, 2);
lean_inc_ref(v_ngen_3476_);
lean_dec(v___x_3475_);
v_namePrefix_3477_ = lean_ctor_get(v_ngen_3476_, 0);
v_idx_3478_ = lean_ctor_get(v_ngen_3476_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_ngen_3476_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3480_ = v_ngen_3476_;
v_isShared_3481_ = v_isSharedCheck_3508_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_idx_3478_);
lean_inc(v_namePrefix_3477_);
lean_dec(v_ngen_3476_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3508_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_r_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
lean_inc(v_idx_3478_);
lean_inc(v_namePrefix_3477_);
v_r_3482_ = l_Lean_Name_num___override(v_namePrefix_3477_, v_idx_3478_);
v___x_3483_ = lean_unsigned_to_nat(1u);
v___x_3484_ = lean_nat_add(v_idx_3478_, v___x_3483_);
lean_dec(v_idx_3478_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 1, v___x_3484_);
v___x_3486_ = v___x_3480_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_namePrefix_3477_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; lean_object* v_env_3488_; lean_object* v_nextMacroScope_3489_; lean_object* v_auxDeclNGen_3490_; lean_object* v_traceState_3491_; lean_object* v_cache_3492_; lean_object* v_recordedDeps_3493_; lean_object* v_messages_3494_; lean_object* v_infoState_3495_; lean_object* v_snapshotTasks_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3505_; 
v___x_3487_ = lean_st_ref_take(v___y_3473_);
v_env_3488_ = lean_ctor_get(v___x_3487_, 0);
v_nextMacroScope_3489_ = lean_ctor_get(v___x_3487_, 1);
v_auxDeclNGen_3490_ = lean_ctor_get(v___x_3487_, 3);
v_traceState_3491_ = lean_ctor_get(v___x_3487_, 4);
v_cache_3492_ = lean_ctor_get(v___x_3487_, 5);
v_recordedDeps_3493_ = lean_ctor_get(v___x_3487_, 6);
v_messages_3494_ = lean_ctor_get(v___x_3487_, 7);
v_infoState_3495_ = lean_ctor_get(v___x_3487_, 8);
v_snapshotTasks_3496_ = lean_ctor_get(v___x_3487_, 9);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; 
v_unused_3506_ = lean_ctor_get(v___x_3487_, 2);
lean_dec(v_unused_3506_);
v___x_3498_ = v___x_3487_;
v_isShared_3499_ = v_isSharedCheck_3505_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_snapshotTasks_3496_);
lean_inc(v_infoState_3495_);
lean_inc(v_messages_3494_);
lean_inc(v_recordedDeps_3493_);
lean_inc(v_cache_3492_);
lean_inc(v_traceState_3491_);
lean_inc(v_auxDeclNGen_3490_);
lean_inc(v_nextMacroScope_3489_);
lean_inc(v_env_3488_);
lean_dec(v___x_3487_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3505_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 2, v___x_3486_);
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_env_3488_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_nextMacroScope_3489_);
lean_ctor_set(v_reuseFailAlloc_3504_, 2, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3504_, 3, v_auxDeclNGen_3490_);
lean_ctor_set(v_reuseFailAlloc_3504_, 4, v_traceState_3491_);
lean_ctor_set(v_reuseFailAlloc_3504_, 5, v_cache_3492_);
lean_ctor_set(v_reuseFailAlloc_3504_, 6, v_recordedDeps_3493_);
lean_ctor_set(v_reuseFailAlloc_3504_, 7, v_messages_3494_);
lean_ctor_set(v_reuseFailAlloc_3504_, 8, v_infoState_3495_);
lean_ctor_set(v_reuseFailAlloc_3504_, 9, v_snapshotTasks_3496_);
v___x_3501_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = lean_st_ref_put(v___y_3473_, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_r_3482_);
return v___x_3503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3509_);
lean_dec(v___y_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v___x_3519_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3517_);
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec(v___y_3528_);
return v_res_3535_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3538_ = l_Lean_stringToMessageData(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3541_ = l_Lean_stringToMessageData(v___x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3544_, lean_object* v_x_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v___x_3553_; lean_object* v___y_3555_; uint8_t v___x_3564_; 
v___x_3553_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3564_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3546_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; 
v___x_3565_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3555_ = v___x_3565_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3566_; 
v___x_3566_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3555_ = v___x_3566_;
goto v___jp_3554_;
}
v___jp_3554_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_inc_ref(v___y_3555_);
v___x_3556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___y_3555_);
v___x_3557_ = l_Lean_MessageData_ofFormat(v___x_3556_);
v___x_3558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3553_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Lean_indentExpr(v_e_3544_);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
return v___x_3563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3567_, lean_object* v_x_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3567_, v_x_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v_x_3568_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3577_, lean_object* v_x_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_keyedConfig_3586_; uint8_t v_trackZetaDelta_3587_; lean_object* v_zetaDeltaSet_3588_; lean_object* v_localInstances_3589_; lean_object* v_defEqCtx_x3f_3590_; lean_object* v_synthPendingDepth_3591_; lean_object* v_customCanUnfoldPredicate_x3f_3592_; uint8_t v_univApprox_3593_; uint8_t v_inTypeClassResolution_3594_; uint8_t v_cacheInferType_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_keyedConfig_3586_ = lean_ctor_get(v___y_3581_, 0);
v_trackZetaDelta_3587_ = lean_ctor_get_uint8(v___y_3581_, sizeof(void*)*7);
v_zetaDeltaSet_3588_ = lean_ctor_get(v___y_3581_, 1);
v_localInstances_3589_ = lean_ctor_get(v___y_3581_, 3);
v_defEqCtx_x3f_3590_ = lean_ctor_get(v___y_3581_, 4);
v_synthPendingDepth_3591_ = lean_ctor_get(v___y_3581_, 5);
v_customCanUnfoldPredicate_x3f_3592_ = lean_ctor_get(v___y_3581_, 6);
v_univApprox_3593_ = lean_ctor_get_uint8(v___y_3581_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3594_ = lean_ctor_get_uint8(v___y_3581_, sizeof(void*)*7 + 2);
v_cacheInferType_3595_ = lean_ctor_get_uint8(v___y_3581_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3592_);
lean_inc(v_synthPendingDepth_3591_);
lean_inc(v_defEqCtx_x3f_3590_);
lean_inc_ref(v_localInstances_3589_);
lean_inc(v_zetaDeltaSet_3588_);
lean_inc_ref(v_keyedConfig_3586_);
v___x_3596_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3596_, 0, v_keyedConfig_3586_);
lean_ctor_set(v___x_3596_, 1, v_zetaDeltaSet_3588_);
lean_ctor_set(v___x_3596_, 2, v_lctx_3577_);
lean_ctor_set(v___x_3596_, 3, v_localInstances_3589_);
lean_ctor_set(v___x_3596_, 4, v_defEqCtx_x3f_3590_);
lean_ctor_set(v___x_3596_, 5, v_synthPendingDepth_3591_);
lean_ctor_set(v___x_3596_, 6, v_customCanUnfoldPredicate_x3f_3592_);
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*7, v_trackZetaDelta_3587_);
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*7 + 1, v_univApprox_3593_);
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3594_);
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*7 + 3, v_cacheInferType_3595_);
lean_inc(v___y_3584_);
lean_inc_ref(v___y_3583_);
lean_inc(v___y_3582_);
lean_inc(v___y_3580_);
lean_inc(v___y_3579_);
v___x_3597_ = lean_apply_7(v_x_3578_, v___y_3579_, v___y_3580_, v___x_3596_, v___y_3582_, v___y_3583_, v___y_3584_, lean_box(0));
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
else
{
return v___x_3597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3606_, lean_object* v_x_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3606_, v_x_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3618_, lean_object* v_letFVars_3619_, lean_object* v_lctx_3620_, lean_object* v_v_3621_, lean_object* v_e_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3630_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3631_ = lean_expr_instantiate_rev(v_e_3622_, v_fvars_3618_);
v___x_3632_ = lean_apply_1(v_v_3621_, v___x_3631_);
v___x_3633_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3633_, 0, lean_box(0));
lean_closure_set(v___x_3633_, 1, v_letFVars_3619_);
lean_closure_set(v___x_3633_, 2, v___x_3632_);
v___x_3634_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3620_, v___x_3630_, v___x_3633_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3635_, lean_object* v_letFVars_3636_, lean_object* v_lctx_3637_, lean_object* v_v_3638_, lean_object* v_e_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3635_, v_letFVars_3636_, v_lctx_3637_, v_v_3638_, v_e_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v_e_3639_);
lean_dec_ref(v_fvars_3635_);
return v_res_3647_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; 
lean_inc_ref(v_a_3651_);
v___x_3660_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3651_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v_expr_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3712_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v_expr_3662_ = lean_ctor_get(v_a_3652_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_a_3652_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; 
v_unused_3713_ = lean_ctor_get(v_a_3652_, 1);
lean_dec(v_unused_3713_);
v___x_3664_ = v_a_3652_;
v_isShared_3665_ = v_isSharedCheck_3712_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_expr_3662_);
lean_dec(v_a_3652_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3712_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; 
lean_inc(v_a_3661_);
lean_inc_ref(v_expr_3662_);
v___x_3666_ = l_Lean_Meta_isExprDefEq(v_expr_3662_, v_a_3661_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3703_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3703_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3703_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
uint8_t v___x_3671_; 
v___x_3671_ = lean_unbox(v_a_3667_);
lean_dec(v_a_3667_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_del_object(v___x_3669_);
v___x_3672_ = lean_box(0);
v___x_3673_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3674_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3661_, v_expr_3662_, v___x_3672_, v___x_3673_, v___y_3655_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v_expr_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3689_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___x_3674_, 1);
v_expr_3676_ = lean_ctor_get(v_a_3651_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3651_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_a_3651_, 1);
lean_dec(v_unused_3690_);
v___x_3678_ = v_a_3651_;
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_expr_3676_);
lean_dec(v_a_3651_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3680_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3681_ = l_Lean_indentExpr(v_expr_3676_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 7);
lean_ctor_set(v___x_3678_, 1, v___x_3681_);
lean_ctor_set(v___x_3678_, 0, v___x_3680_);
v___x_3683_ = v___x_3678_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3685_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set_tag(v___x_3664_, 7);
lean_ctor_set(v___x_3664_, 1, v_a_3675_);
lean_ctor_set(v___x_3664_, 0, v___x_3683_);
v___x_3685_ = v___x_3664_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_a_3675_);
v___x_3685_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3685_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
return v___x_3686_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_del_object(v___x_3664_);
lean_dec_ref(v_a_3651_);
v_a_3691_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3674_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3674_);
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
else
{
lean_object* v___x_3699_; lean_object* v___x_3701_; 
lean_del_object(v___x_3664_);
lean_dec_ref(v_expr_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3651_);
v___x_3699_ = lean_box(0);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3699_);
v___x_3701_ = v___x_3669_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_del_object(v___x_3664_);
lean_dec_ref(v_expr_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3651_);
v_a_3704_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3666_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3666_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec_ref(v_a_3652_);
lean_dec_ref(v_a_3651_);
v_a_3714_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3660_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3660_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3722_, v_a_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
return v_res_3731_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3734_ = l_Lean_stringToMessageData(v___x_3733_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
if (lean_obj_tag(v_e_3735_) == 5)
{
lean_object* v_fn_3743_; lean_object* v_arg_3744_; lean_object* v___x_3745_; 
v_fn_3743_ = lean_ctor_get(v_e_3735_, 0);
v_arg_3744_ = lean_ctor_get(v_e_3735_, 1);
lean_inc_ref(v_fn_3743_);
v___x_3745_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3743_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
lean_inc_ref(v_arg_3744_);
v___x_3747_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3744_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3770_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3770_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3770_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v_expr_3752_; size_t v___x_3753_; size_t v___x_3754_; uint8_t v___x_3755_; 
v_expr_3752_ = lean_ctor_get(v_a_3748_, 0);
lean_inc_ref(v_expr_3752_);
lean_dec(v_a_3748_);
v___x_3753_ = lean_ptr_addr(v_fn_3743_);
v___x_3754_ = lean_ptr_addr(v_a_3746_);
v___x_3755_ = lean_usize_dec_eq(v___x_3753_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec_ref_known(v_e_3735_, 2);
v___x_3756_ = l_Lean_Expr_app___override(v_a_3746_, v_expr_3752_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3756_);
v___x_3758_ = v___x_3750_;
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
size_t v___x_3760_; size_t v___x_3761_; uint8_t v___x_3762_; 
v___x_3760_ = lean_ptr_addr(v_arg_3744_);
v___x_3761_ = lean_ptr_addr(v_expr_3752_);
v___x_3762_ = lean_usize_dec_eq(v___x_3760_, v___x_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; lean_object* v___x_3765_; 
lean_dec_ref_known(v_e_3735_, 2);
v___x_3763_ = l_Lean_Expr_app___override(v_a_3746_, v_expr_3752_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3763_);
v___x_3765_ = v___x_3750_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
else
{
lean_object* v___x_3768_; 
lean_dec_ref(v_expr_3752_);
lean_dec(v_a_3746_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v_e_3735_);
v___x_3768_ = v___x_3750_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_e_3735_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v_a_3746_);
lean_dec_ref_known(v_e_3735_, 2);
v_a_3771_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3747_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3747_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3735_, 2);
return v___x_3745_;
}
}
else
{
lean_object* v___x_3779_; 
v___x_3779_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3788_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3782_ = v___x_3779_;
v_isShared_3783_ = v_isSharedCheck_3788_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3788_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v_expr_3784_; lean_object* v___x_3786_; 
v_expr_3784_ = lean_ctor_get(v_a_3780_, 0);
lean_inc_ref(v_expr_3784_);
lean_dec(v_a_3780_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v_expr_3784_);
v___x_3786_ = v___x_3782_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_expr_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
v_a_3789_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3779_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3779_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_a_3803_);
lean_dec_ref(v_a_3802_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
lean_dec(v_a_3799_);
lean_dec(v_a_3798_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
if (lean_obj_tag(v_e_3806_) == 5)
{
lean_object* v_fn_3814_; lean_object* v_arg_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_fn_3814_ = lean_ctor_get(v_e_3806_, 0);
v_arg_3815_ = lean_ctor_get(v_e_3806_, 1);
lean_inc_ref_n(v_fn_3814_, 2);
v___x_3816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3816_, 0, v_fn_3814_);
v___x_3817_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3814_, v___x_3816_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
lean_inc_ref(v_arg_3815_);
v___x_3819_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3815_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
v___x_3821_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3806_, v_a_3818_, v_a_3820_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
return v___x_3821_;
}
else
{
lean_dec(v_a_3818_);
lean_dec_ref_known(v_e_3806_, 2);
return v___x_3819_;
}
}
else
{
lean_dec_ref_known(v_e_3806_, 2);
return v___x_3817_;
}
}
else
{
lean_object* v___x_3822_; 
v___x_3822_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
return v___x_3822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
uint8_t v___x_3831_; 
v___x_3831_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3824_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; 
v___x_3832_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3842_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3837_ = lean_box(0);
v___x_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3838_, 0, v_a_3833_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3838_);
v___x_3840_ = v___x_3835_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
v_a_3843_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3832_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3832_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
else
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_Expr_getAppFn(v_e_3823_);
if (lean_obj_tag(v___x_3851_) == 2)
{
lean_object* v_mvarId_3852_; lean_object* v_dummy_3853_; lean_object* v_nargs_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_mvarId_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_mvarId_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v_dummy_3853_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3854_ = l_Lean_Expr_getAppNumArgs(v_e_3823_);
lean_inc(v_nargs_3854_);
v___x_3855_ = lean_mk_array(v_nargs_3854_, v_dummy_3853_);
v___x_3856_ = lean_unsigned_to_nat(1u);
v___x_3857_ = lean_nat_sub(v_nargs_3854_, v___x_3856_);
lean_dec(v_nargs_3854_);
lean_inc_ref(v_e_3823_);
v___x_3858_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3823_, v___x_3855_, v___x_3857_);
v___x_3859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3852_, v___x_3858_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
lean_dec(v_mvarId_3852_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v___x_3860_; 
lean_dec_ref_known(v___x_3859_, 1);
v___x_3860_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3860_;
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_e_3823_);
v_a_3861_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3859_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3859_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v___x_3869_; 
lean_dec_ref(v___x_3851_);
v___x_3869_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec(v_a_3871_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3889_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3888_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
return v___x_3889_;
}
else
{
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec(v_a_3891_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3899_, lean_object* v_fvars_3900_, lean_object* v_doms_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3899_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3900_, v_doms_3901_, v_a_3910_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
return v___x_3911_;
}
else
{
return v___x_3909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3912_, lean_object* v_fvars_3913_, lean_object* v_doms_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3912_, v_fvars_3913_, v_doms_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v_doms_3914_);
lean_dec_ref(v_fvars_3913_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3923_, lean_object* v_fvars_3924_, lean_object* v_doms_3925_, lean_object* v_e_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3926_, v_a_3928_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
if (lean_obj_tag(v_a_3935_) == 1)
{
lean_object* v_val_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_dec_ref(v_e_3926_);
v_val_3936_ = lean_ctor_get(v_a_3935_, 0);
lean_inc(v_val_3936_);
lean_dec_ref_known(v_a_3935_, 1);
v___x_3937_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3938_, 0, v_fvars_3924_);
lean_closure_set(v___x_3938_, 1, v_doms_3925_);
lean_closure_set(v___x_3938_, 2, v_val_3936_);
v___x_3939_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3923_, v___x_3937_, v___x_3938_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
return v___x_3939_;
}
else
{
lean_dec(v_a_3935_);
if (lean_obj_tag(v_e_3926_) == 7)
{
lean_object* v_binderName_3940_; lean_object* v_binderType_3941_; lean_object* v_body_3942_; uint8_t v_binderInfo_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_binderName_3940_ = lean_ctor_get(v_e_3926_, 0);
lean_inc(v_binderName_3940_);
v_binderType_3941_ = lean_ctor_get(v_e_3926_, 1);
lean_inc_ref(v_binderType_3941_);
v_body_3942_ = lean_ctor_get(v_e_3926_, 2);
lean_inc_ref(v_body_3942_);
v_binderInfo_3943_ = lean_ctor_get_uint8(v_e_3926_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3926_, 3);
v___x_3944_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3945_ = lean_expr_instantiate_rev(v_binderType_3941_, v_fvars_3924_);
lean_dec_ref(v_binderType_3941_);
v___x_3946_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3946_, 0, v___x_3945_);
lean_inc_ref(v_lctx_3923_);
v___x_3947_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3923_, v___x_3944_, v___x_3946_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3949_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v___x_3947_, 1);
v___x_3949_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v_expr_3951_; uint8_t v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc_n(v_a_3950_, 2);
lean_dec_ref_known(v___x_3949_, 1);
v_expr_3951_ = lean_ctor_get(v_a_3948_, 0);
v___x_3952_ = 0;
lean_inc_ref(v_expr_3951_);
v___x_3953_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3923_, v_a_3950_, v_binderName_3940_, v_expr_3951_, v_binderInfo_3943_, v___x_3952_);
v___x_3954_ = l_Lean_Expr_fvar___override(v_a_3950_);
v___x_3955_ = lean_array_push(v_fvars_3924_, v___x_3954_);
v___x_3956_ = lean_array_push(v_doms_3925_, v_a_3948_);
v_lctx_3923_ = v___x_3953_;
v_fvars_3924_ = v___x_3955_;
v_doms_3925_ = v___x_3956_;
v_e_3926_ = v_body_3942_;
goto _start;
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec(v_a_3948_);
lean_dec_ref(v_body_3942_);
lean_dec(v_binderName_3940_);
lean_dec_ref(v_doms_3925_);
lean_dec_ref(v_fvars_3924_);
lean_dec_ref(v_lctx_3923_);
v_a_3958_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3949_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3949_);
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
lean_dec_ref(v_body_3942_);
lean_dec(v_binderName_3940_);
lean_dec_ref(v_doms_3925_);
lean_dec_ref(v_fvars_3924_);
lean_dec_ref(v_lctx_3923_);
return v___x_3947_;
}
}
else
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___f_3968_; lean_object* v___x_3969_; 
v___x_3966_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3967_ = lean_expr_instantiate_rev(v_e_3926_, v_fvars_3924_);
lean_dec_ref(v_e_3926_);
v___f_3968_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3968_, 0, v___x_3967_);
lean_closure_set(v___f_3968_, 1, v_fvars_3924_);
lean_closure_set(v___f_3968_, 2, v_doms_3925_);
v___x_3969_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3923_, v___x_3966_, v___f_3968_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
return v___x_3969_;
}
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec_ref(v_e_3926_);
lean_dec_ref(v_doms_3925_);
lean_dec_ref(v_fvars_3924_);
lean_dec_ref(v_lctx_3923_);
v_a_3970_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3934_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3934_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
uint32_t v___x_3986_; uint8_t v___x_3987_; 
v___x_3986_ = 5;
v___x_3987_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3978_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v_lctx_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_lctx_3988_ = lean_ctor_get(v_a_3981_, 2);
v___x_3989_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3988_);
v___x_3990_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3988_, v___x_3989_, v___x_3989_, v_e_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
return v___x_3990_;
}
else
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3991_ = lean_box(0);
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v_e_3978_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
return v___x_3993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec(v_a_3995_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_4003_, lean_object* v_e_4004_, lean_object* v_typeName_4005_, lean_object* v_idx_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4003_, v_e_4004_, v_typeName_4005_, v_idx_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec(v___y_4007_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec(v_a_4016_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v___x_4035_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4024_, v_a_4034_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4035_;
}
else
{
lean_dec_ref(v_fvars_4024_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4046_, lean_object* v_fvars_4047_, lean_object* v_e_4048_, lean_object* v_letFVars_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
switch(lean_obj_tag(v_e_4048_))
{
case 6:
{
lean_object* v_binderName_4057_; lean_object* v_binderType_4058_; lean_object* v_body_4059_; uint8_t v_binderInfo_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_binderName_4057_ = lean_ctor_get(v_e_4048_, 0);
lean_inc(v_binderName_4057_);
v_binderType_4058_ = lean_ctor_get(v_e_4048_, 1);
lean_inc_ref(v_binderType_4058_);
v_body_4059_ = lean_ctor_get(v_e_4048_, 2);
lean_inc_ref(v_body_4059_);
v_binderInfo_4060_ = lean_ctor_get_uint8(v_e_4048_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4048_, 3);
v___x_4061_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4046_);
lean_inc(v_letFVars_4049_);
v___x_4062_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4047_, v_letFVars_4049_, v_lctx_4046_, v___x_4061_, v_binderType_4058_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
lean_dec_ref(v_binderType_4058_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4064_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v___x_4064_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v_expr_4066_; uint8_t v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc_n(v_a_4065_, 2);
lean_dec_ref_known(v___x_4064_, 1);
v_expr_4066_ = lean_ctor_get(v_a_4063_, 0);
lean_inc_ref(v_expr_4066_);
lean_dec(v_a_4063_);
v___x_4067_ = 0;
v___x_4068_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4046_, v_a_4065_, v_binderName_4057_, v_expr_4066_, v_binderInfo_4060_, v___x_4067_);
v___x_4069_ = l_Lean_Expr_fvar___override(v_a_4065_);
v___x_4070_ = lean_array_push(v_fvars_4047_, v___x_4069_);
v_lctx_4046_ = v___x_4068_;
v_fvars_4047_ = v___x_4070_;
v_e_4048_ = v_body_4059_;
goto _start;
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
lean_dec(v_a_4063_);
lean_dec_ref(v_body_4059_);
lean_dec(v_binderName_4057_);
lean_dec(v_letFVars_4049_);
lean_dec_ref(v_fvars_4047_);
lean_dec_ref(v_lctx_4046_);
v_a_4072_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___x_4064_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4064_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
else
{
lean_dec_ref(v_body_4059_);
lean_dec(v_binderName_4057_);
lean_dec(v_letFVars_4049_);
lean_dec_ref(v_fvars_4047_);
lean_dec_ref(v_lctx_4046_);
return v___x_4062_;
}
}
case 8:
{
lean_object* v_declName_4080_; lean_object* v_type_4081_; lean_object* v_value_4082_; lean_object* v_body_4083_; uint8_t v_nondep_4084_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v_declName_4080_ = lean_ctor_get(v_e_4048_, 0);
lean_inc(v_declName_4080_);
v_type_4081_ = lean_ctor_get(v_e_4048_, 1);
lean_inc_ref(v_type_4081_);
v_value_4082_ = lean_ctor_get(v_e_4048_, 2);
lean_inc_ref(v_value_4082_);
v_body_4083_ = lean_ctor_get(v_e_4048_, 3);
lean_inc_ref(v_body_4083_);
v_nondep_4084_ = lean_ctor_get_uint8(v_e_4048_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4048_, 4);
v___x_4098_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4046_);
lean_inc(v_letFVars_4049_);
v___x_4099_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4047_, v_letFVars_4049_, v_lctx_4046_, v___x_4098_, v_type_4081_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
lean_dec_ref(v_type_4081_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4099_, 1);
v___x_4101_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4046_);
lean_inc(v_letFVars_4049_);
v___x_4102_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4047_, v_letFVars_4049_, v_lctx_4046_, v___x_4101_, v_value_4082_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
lean_dec_ref(v_value_4082_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; uint8_t v___x_4133_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4102_, 1);
v___x_4133_ = l_List_isEmpty___redArg(v_letFVars_4049_);
if (v___x_4133_ == 0)
{
lean_object* v___f_4134_; lean_object* v___x_4135_; 
lean_inc(v_a_4100_);
lean_inc(v_a_4103_);
v___f_4134_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4134_, 0, v_a_4103_);
lean_closure_set(v___f_4134_, 1, v_a_4100_);
lean_inc_ref(v_lctx_4046_);
v___x_4135_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4046_, v___f_4134_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_dec_ref_known(v___x_4135_, 1);
v___y_4105_ = v_a_4050_;
v___y_4106_ = v_a_4051_;
v___y_4107_ = v_a_4052_;
v___y_4108_ = v_a_4053_;
v___y_4109_ = v_a_4054_;
v___y_4110_ = v_a_4055_;
goto v___jp_4104_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_a_4103_);
lean_dec(v_a_4100_);
lean_dec_ref(v_body_4083_);
lean_dec(v_declName_4080_);
lean_dec(v_letFVars_4049_);
lean_dec_ref(v_fvars_4047_);
lean_dec_ref(v_lctx_4046_);
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
v___y_4105_ = v_a_4050_;
v___y_4106_ = v_a_4051_;
v___y_4107_ = v_a_4052_;
v___y_4108_ = v_a_4053_;
v___y_4109_ = v_a_4054_;
v___y_4110_ = v_a_4055_;
goto v___jp_4104_;
}
v___jp_4104_:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v_expr_4113_; lean_object* v_expr_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4123_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v_expr_4113_ = lean_ctor_get(v_a_4100_, 0);
lean_inc_ref(v_expr_4113_);
lean_dec(v_a_4100_);
v_expr_4114_ = lean_ctor_get(v_a_4103_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_a_4103_);
if (v_isSharedCheck_4123_ == 0)
{
lean_object* v_unused_4124_; 
v_unused_4124_ = lean_ctor_get(v_a_4103_, 1);
lean_dec(v_unused_4124_);
v___x_4116_ = v_a_4103_;
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_expr_4114_);
lean_dec(v_a_4103_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
uint8_t v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = 0;
lean_inc(v_a_4112_);
v___x_4119_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4046_, v_a_4112_, v_declName_4080_, v_expr_4113_, v_expr_4114_, v_nondep_4084_, v___x_4118_);
if (v_nondep_4084_ == 0)
{
lean_object* v___x_4121_; 
lean_inc(v_a_4112_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 1);
lean_ctor_set(v___x_4116_, 1, v_letFVars_4049_);
lean_ctor_set(v___x_4116_, 0, v_a_4112_);
v___x_4121_ = v___x_4116_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4112_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_letFVars_4049_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
v___y_4086_ = v___y_4110_;
v___y_4087_ = v___x_4119_;
v___y_4088_ = v___y_4109_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4107_;
v___y_4091_ = v___y_4106_;
v___y_4092_ = v___y_4105_;
v___y_4093_ = v_a_4112_;
v___y_4094_ = v___x_4121_;
goto v___jp_4085_;
}
}
else
{
lean_del_object(v___x_4116_);
v___y_4086_ = v___y_4110_;
v___y_4087_ = v___x_4119_;
v___y_4088_ = v___y_4109_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4107_;
v___y_4091_ = v___y_4106_;
v___y_4092_ = v___y_4105_;
v___y_4093_ = v_a_4112_;
v___y_4094_ = v_letFVars_4049_;
goto v___jp_4085_;
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec(v_a_4103_);
lean_dec(v_a_4100_);
lean_dec_ref(v_body_4083_);
lean_dec(v_declName_4080_);
lean_dec(v_letFVars_4049_);
lean_dec_ref(v_fvars_4047_);
lean_dec_ref(v_lctx_4046_);
v_a_4125_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4111_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4111_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
else
{
lean_dec(v_a_4100_);
lean_dec_ref(v_body_4083_);
lean_dec(v_declName_4080_);
lean_dec(v_letFVars_4049_);
lean_dec_ref(v_fvars_4047_);
lean_dec_ref(v_lctx_4046_);
return v___x_4102_;
}
}
else
{
lean_dec_ref(v_body_4083_);
lean_dec_ref(v_value_4082_);
lean_dec(v_declName_4080_);
lean_dec(v_letFVars_4049_);
lean_dec_ref(v_fvars_4047_);
lean_dec_ref(v_lctx_4046_);
return v___x_4099_;
}
v___jp_4085_:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = l_Lean_Expr_fvar___override(v___y_4093_);
v___x_4096_ = lean_array_push(v_fvars_4047_, v___x_4095_);
v_lctx_4046_ = v___y_4087_;
v_fvars_4047_ = v___x_4096_;
v_e_4048_ = v_body_4083_;
v_letFVars_4049_ = v___y_4094_;
v_a_4050_ = v___y_4092_;
v_a_4051_ = v___y_4091_;
v_a_4052_ = v___y_4090_;
v_a_4053_ = v___y_4089_;
v_a_4054_ = v___y_4088_;
v_a_4055_ = v___y_4086_;
goto _start;
}
}
default: 
{
lean_object* v___f_4144_; lean_object* v___x_4145_; 
lean_inc_ref(v_fvars_4047_);
v___f_4144_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4144_, 0, v_fvars_4047_);
v___x_4145_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4047_, v_letFVars_4049_, v_lctx_4046_, v___f_4144_, v_e_4048_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
lean_dec_ref(v_e_4048_);
lean_dec_ref(v_fvars_4047_);
return v___x_4145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
uint32_t v___x_4154_; uint8_t v___x_4155_; 
v___x_4154_ = 5;
v___x_4155_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4146_, v___x_4154_);
if (v___x_4155_ == 0)
{
lean_object* v_lctx_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_lctx_4156_ = lean_ctor_get(v_a_4149_, 2);
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4147_);
lean_inc_ref(v_lctx_4156_);
v___x_4158_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4156_, v___x_4157_, v_e_4146_, v_a_4147_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
return v___x_4158_;
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4159_ = lean_box(0);
v___x_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4160_, 0, v_e_4146_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
return v___x_4161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
lean_dec(v_a_4164_);
lean_dec(v_a_4163_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
switch(lean_obj_tag(v_e_4171_))
{
case 0:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4179_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4180_ = l_Lean_MessageData_ofExpr(v_e_4171_);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4181_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4182_;
}
case 1:
{
lean_object* v___x_4183_; 
v___x_4183_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4171_, v___y_4174_, v___y_4176_, v___y_4177_);
return v___x_4183_;
}
case 2:
{
lean_object* v___x_4184_; 
v___x_4184_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4184_;
}
case 3:
{
lean_object* v_u_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_u_4185_ = lean_ctor_get(v_e_4171_, 0);
lean_inc(v_u_4185_);
v___x_4186_ = l_Lean_Level_succ___override(v_u_4185_);
v___x_4187_ = l_Lean_Expr_sort___override(v___x_4186_);
v___x_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
v___x_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4189_, 0, v_e_4171_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
case 4:
{
lean_object* v___x_4191_; 
v___x_4191_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4191_;
}
case 5:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
lean_inc_ref(v_e_4171_);
v___x_4192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4192_, 0, v_e_4171_);
v___x_4193_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4171_, v___x_4192_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4193_;
}
case 7:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_inc_ref(v_e_4171_);
v___x_4194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4194_, 0, v_e_4171_);
v___x_4195_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4171_, v___x_4194_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4195_;
}
case 9:
{
lean_object* v_a_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_a_4196_ = lean_ctor_get(v_e_4171_, 0);
v___x_4197_ = l_Lean_Literal_type(v_a_4196_);
v___x_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
v___x_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4199_, 0, v_e_4171_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
return v___x_4200_;
}
case 10:
{
lean_object* v_data_4201_; lean_object* v_expr_4202_; lean_object* v___x_4203_; 
v_data_4201_ = lean_ctor_get(v_e_4171_, 0);
v_expr_4202_ = lean_ctor_get(v_e_4171_, 1);
lean_inc_ref(v_expr_4202_);
v___x_4203_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4202_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4226_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4226_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4226_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v_expr_4208_; lean_object* v_type_x3f_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4225_; 
v_expr_4208_ = lean_ctor_get(v_a_4204_, 0);
v_type_x3f_4209_ = lean_ctor_get(v_a_4204_, 1);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_a_4204_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4211_ = v_a_4204_;
v_isShared_4212_ = v_isSharedCheck_4225_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_type_x3f_4209_);
lean_inc(v_expr_4208_);
lean_dec(v_a_4204_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4225_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___y_4214_; size_t v___x_4221_; size_t v___x_4222_; uint8_t v___x_4223_; 
v___x_4221_ = lean_ptr_addr(v_expr_4202_);
v___x_4222_ = lean_ptr_addr(v_expr_4208_);
v___x_4223_ = lean_usize_dec_eq(v___x_4221_, v___x_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; 
lean_inc(v_data_4201_);
lean_dec_ref_known(v_e_4171_, 2);
v___x_4224_ = l_Lean_Expr_mdata___override(v_data_4201_, v_expr_4208_);
v___y_4214_ = v___x_4224_;
goto v___jp_4213_;
}
else
{
lean_dec_ref(v_expr_4208_);
v___y_4214_ = v_e_4171_;
goto v___jp_4213_;
}
v___jp_4213_:
{
lean_object* v___x_4216_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___y_4214_);
v___x_4216_ = v___x_4211_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___y_4214_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_type_x3f_4209_);
v___x_4216_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4218_; 
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4216_);
v___x_4218_ = v___x_4206_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4171_, 2);
return v___x_4203_;
}
}
case 11:
{
lean_object* v_typeName_4227_; lean_object* v_idx_4228_; lean_object* v_struct_4229_; lean_object* v___f_4230_; lean_object* v___x_4231_; 
v_typeName_4227_ = lean_ctor_get(v_e_4171_, 0);
v_idx_4228_ = lean_ctor_get(v_e_4171_, 1);
v_struct_4229_ = lean_ctor_get(v_e_4171_, 2);
lean_inc(v_idx_4228_);
lean_inc(v_typeName_4227_);
lean_inc_ref(v_e_4171_);
lean_inc_ref(v_struct_4229_);
v___f_4230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4230_, 0, v_struct_4229_);
lean_closure_set(v___f_4230_, 1, v_e_4171_);
lean_closure_set(v___f_4230_, 2, v_typeName_4227_);
lean_closure_set(v___f_4230_, 3, v_idx_4228_);
v___x_4231_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4171_, v___f_4230_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4231_;
}
default: 
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_inc_ref(v_e_4171_);
v___x_4232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4232_, 0, v_e_4171_);
v___x_4233_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4171_, v___x_4232_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4233_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4234_; double v___x_4235_; 
v___x_4234_ = lean_unsigned_to_nat(1000000000u);
v___x_4235_ = lean_float_of_nat(v___x_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v_toCold_4244_; lean_object* v_options_4245_; uint8_t v_hasTrace_4246_; 
v_toCold_4244_ = lean_ctor_get(v_a_4241_, 0);
v_options_4245_ = lean_ctor_get(v_toCold_4244_, 2);
v_hasTrace_4246_ = lean_ctor_get_uint8(v_options_4245_, sizeof(void*)*1);
if (v_hasTrace_4246_ == 0)
{
lean_object* v___x_4247_; 
v___x_4247_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
return v___x_4247_;
}
else
{
lean_object* v_inheritedTraceOptions_4248_; lean_object* v___f_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v_a_4257_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v_a_4272_; 
v_inheritedTraceOptions_4248_ = lean_ctor_get(v_toCold_4244_, 11);
lean_inc_ref(v_e_4236_);
v___f_4249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4249_, 0, v_e_4236_);
v___x_4250_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4251_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4252_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4248_, v_options_4245_, v___x_4252_);
if (v___x_4253_ == 0)
{
lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4330_ = l_Lean_trace_profiler;
v___x_4331_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4245_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; 
lean_dec_ref(v___f_4249_);
v___x_4332_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
return v___x_4332_;
}
else
{
goto v___jp_4281_;
}
}
else
{
goto v___jp_4281_;
}
v___jp_4254_:
{
lean_object* v___x_4258_; double v___x_4259_; double v___x_4260_; double v___x_4261_; double v___x_4262_; double v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4258_ = lean_io_mono_nanos_now();
v___x_4259_ = lean_float_of_nat(v___y_4255_);
v___x_4260_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4261_ = lean_float_div(v___x_4259_, v___x_4260_);
v___x_4262_ = lean_float_of_nat(v___x_4258_);
v___x_4263_ = lean_float_div(v___x_4262_, v___x_4260_);
v___x_4264_ = lean_box_float(v___x_4261_);
v___x_4265_ = lean_box_float(v___x_4263_);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4264_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4267_, 0, v_a_4257_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4250_, v_hasTrace_4246_, v___x_4251_, v_options_4245_, v___x_4253_, v___y_4256_, v___f_4249_, v___x_4267_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
return v___x_4268_;
}
v___jp_4269_:
{
lean_object* v___x_4273_; double v___x_4274_; double v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4273_ = lean_io_get_num_heartbeats();
v___x_4274_ = lean_float_of_nat(v___y_4270_);
v___x_4275_ = lean_float_of_nat(v___x_4273_);
v___x_4276_ = lean_box_float(v___x_4274_);
v___x_4277_ = lean_box_float(v___x_4275_);
v___x_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v_a_4272_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4250_, v_hasTrace_4246_, v___x_4251_, v_options_4245_, v___x_4253_, v___y_4271_, v___f_4249_, v___x_4279_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
return v___x_4280_;
}
v___jp_4281_:
{
lean_object* v___x_4282_; 
v___x_4282_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4242_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4285_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4245_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_io_mono_nanos_now();
v___x_4287_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 1);
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
v___y_4255_ = v___x_4286_;
v___y_4256_ = v_a_4283_;
v_a_4257_ = v___x_4293_;
goto v___jp_4254_;
}
}
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
v_a_4296_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4298_ = v___x_4287_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4287_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
lean_ctor_set_tag(v___x_4298_, 0);
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
v___y_4255_ = v___x_4286_;
v___y_4256_ = v_a_4283_;
v_a_4257_ = v___x_4301_;
goto v___jp_4254_;
}
}
}
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = lean_io_get_num_heartbeats();
v___x_4305_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set_tag(v___x_4308_, 1);
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
v___y_4270_ = v___x_4304_;
v___y_4271_ = v_a_4283_;
v_a_4272_ = v___x_4311_;
goto v___jp_4269_;
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
v_a_4314_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4305_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4305_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set_tag(v___x_4316_, 0);
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
v___y_4270_ = v___x_4304_;
v___y_4271_ = v_a_4283_;
v_a_4272_ = v___x_4319_;
goto v___jp_4269_;
}
}
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec_ref(v___f_4249_);
lean_dec_ref(v_e_4236_);
v_a_4322_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4282_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4282_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4333_, lean_object* v_e_4334_, lean_object* v_typeName_4335_, lean_object* v_idx_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4333_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4346_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4344_, 1);
v___x_4346_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4334_, v_typeName_4335_, v_idx_4336_, v_a_4345_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
return v___x_4346_;
}
else
{
lean_dec(v_idx_4336_);
lean_dec(v_typeName_4335_);
lean_dec_ref(v_e_4334_);
return v___x_4344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
lean_dec(v_a_4353_);
lean_dec_ref(v_a_4352_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec(v_a_4348_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4356_, lean_object* v_fvars_4357_, lean_object* v_doms_4358_, lean_object* v_e_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4356_, v_fvars_4357_, v_doms_4358_, v_e_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_a_4365_);
lean_dec_ref(v_a_4364_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec(v_a_4360_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec(v___y_4369_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4377_, lean_object* v_fvars_4378_, lean_object* v_e_4379_, lean_object* v_letFVars_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4377_, v_fvars_4378_, v_e_4379_, v_letFVars_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec(v_a_4382_);
lean_dec(v_a_4381_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4389_, lean_object* v_lctx_4390_, lean_object* v_localInsts_4391_, lean_object* v_x_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4390_, v_localInsts_4391_, v_x_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4401_, lean_object* v_lctx_4402_, lean_object* v_localInsts_4403_, lean_object* v_x_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4401_, v_lctx_4402_, v_localInsts_4403_, v_x_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec(v___y_4405_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4413_, lean_object* v_lctx_4414_, lean_object* v_x_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4414_, v_x_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4424_, lean_object* v_lctx_4425_, lean_object* v_x_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4424_, v_lctx_4425_, v_x_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec(v___y_4427_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v___x_4442_; 
v___x_4442_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4440_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec(v___y_4443_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4456_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec(v___y_4459_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4467_, lean_object* v_x_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4468_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4477_, lean_object* v_x_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4477_, v_x_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec(v___y_4479_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4487_, lean_object* v_data_4488_, lean_object* v_ref_4489_, lean_object* v_msg_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4487_, v_data_4488_, v_ref_4489_, v_msg_4490_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4499_, lean_object* v_data_4500_, lean_object* v_ref_4501_, lean_object* v_msg_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4499_, v_data_4500_, v_ref_4501_, v_msg_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec(v___y_4503_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(lean_object* v___y_4511_){
_start:
{
lean_object* v___x_4513_; lean_object* v_traceState_4514_; lean_object* v_traces_4515_; lean_object* v___x_4516_; lean_object* v_traceState_4517_; lean_object* v_env_4518_; lean_object* v_nextMacroScope_4519_; lean_object* v_ngen_4520_; lean_object* v_auxDeclNGen_4521_; lean_object* v_cache_4522_; lean_object* v_recordedDeps_4523_; lean_object* v_messages_4524_; lean_object* v_infoState_4525_; lean_object* v_snapshotTasks_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4547_; 
v___x_4513_ = lean_st_ref_get(v___y_4511_);
v_traceState_4514_ = lean_ctor_get(v___x_4513_, 4);
lean_inc_ref(v_traceState_4514_);
lean_dec(v___x_4513_);
v_traces_4515_ = lean_ctor_get(v_traceState_4514_, 0);
lean_inc_ref(v_traces_4515_);
lean_dec_ref(v_traceState_4514_);
v___x_4516_ = lean_st_ref_take(v___y_4511_);
v_traceState_4517_ = lean_ctor_get(v___x_4516_, 4);
v_env_4518_ = lean_ctor_get(v___x_4516_, 0);
v_nextMacroScope_4519_ = lean_ctor_get(v___x_4516_, 1);
v_ngen_4520_ = lean_ctor_get(v___x_4516_, 2);
v_auxDeclNGen_4521_ = lean_ctor_get(v___x_4516_, 3);
v_cache_4522_ = lean_ctor_get(v___x_4516_, 5);
v_recordedDeps_4523_ = lean_ctor_get(v___x_4516_, 6);
v_messages_4524_ = lean_ctor_get(v___x_4516_, 7);
v_infoState_4525_ = lean_ctor_get(v___x_4516_, 8);
v_snapshotTasks_4526_ = lean_ctor_get(v___x_4516_, 9);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4528_ = v___x_4516_;
v_isShared_4529_ = v_isSharedCheck_4547_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_snapshotTasks_4526_);
lean_inc(v_infoState_4525_);
lean_inc(v_messages_4524_);
lean_inc(v_recordedDeps_4523_);
lean_inc(v_cache_4522_);
lean_inc(v_traceState_4517_);
lean_inc(v_auxDeclNGen_4521_);
lean_inc(v_ngen_4520_);
lean_inc(v_nextMacroScope_4519_);
lean_inc(v_env_4518_);
lean_dec(v___x_4516_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4547_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
uint64_t v_tid_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4545_; 
v_tid_4530_ = lean_ctor_get_uint64(v_traceState_4517_, sizeof(void*)*1);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_traceState_4517_);
if (v_isSharedCheck_4545_ == 0)
{
lean_object* v_unused_4546_; 
v_unused_4546_ = lean_ctor_get(v_traceState_4517_, 0);
lean_dec(v_unused_4546_);
v___x_4532_ = v_traceState_4517_;
v_isShared_4533_ = v_isSharedCheck_4545_;
goto v_resetjp_4531_;
}
else
{
lean_dec(v_traceState_4517_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4545_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4534_ = lean_unsigned_to_nat(32u);
v___x_4535_ = lean_mk_empty_array_with_capacity(v___x_4534_);
lean_dec_ref(v___x_4535_);
v___x_4536_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4536_);
v___x_4538_ = v___x_4532_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4536_);
lean_ctor_set_uint64(v_reuseFailAlloc_4544_, sizeof(void*)*1, v_tid_4530_);
v___x_4538_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4540_; 
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 4, v___x_4538_);
v___x_4540_ = v___x_4528_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_env_4518_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_nextMacroScope_4519_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_ngen_4520_);
lean_ctor_set(v_reuseFailAlloc_4543_, 3, v_auxDeclNGen_4521_);
lean_ctor_set(v_reuseFailAlloc_4543_, 4, v___x_4538_);
lean_ctor_set(v_reuseFailAlloc_4543_, 5, v_cache_4522_);
lean_ctor_set(v_reuseFailAlloc_4543_, 6, v_recordedDeps_4523_);
lean_ctor_set(v_reuseFailAlloc_4543_, 7, v_messages_4524_);
lean_ctor_set(v_reuseFailAlloc_4543_, 8, v_infoState_4525_);
lean_ctor_set(v_reuseFailAlloc_4543_, 9, v_snapshotTasks_4526_);
v___x_4540_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_st_ref_put(v___y_4511_, v___x_4540_);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v_traces_4515_);
return v___x_4542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg___boxed(lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v___y_4548_);
lean_dec(v___y_4548_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v___y_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4563_, lean_object* v_msg_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v_ref_4570_; lean_object* v___x_4571_; lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4617_; 
v_ref_4570_ = lean_ctor_get(v___y_4567_, 2);
v___x_4571_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4574_ = v___x_4571_;
v_isShared_4575_ = v_isSharedCheck_4617_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4617_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4576_; lean_object* v_traceState_4577_; lean_object* v_env_4578_; lean_object* v_nextMacroScope_4579_; lean_object* v_ngen_4580_; lean_object* v_auxDeclNGen_4581_; lean_object* v_cache_4582_; lean_object* v_recordedDeps_4583_; lean_object* v_messages_4584_; lean_object* v_infoState_4585_; lean_object* v_snapshotTasks_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4616_; 
v___x_4576_ = lean_st_ref_take(v___y_4568_);
v_traceState_4577_ = lean_ctor_get(v___x_4576_, 4);
v_env_4578_ = lean_ctor_get(v___x_4576_, 0);
v_nextMacroScope_4579_ = lean_ctor_get(v___x_4576_, 1);
v_ngen_4580_ = lean_ctor_get(v___x_4576_, 2);
v_auxDeclNGen_4581_ = lean_ctor_get(v___x_4576_, 3);
v_cache_4582_ = lean_ctor_get(v___x_4576_, 5);
v_recordedDeps_4583_ = lean_ctor_get(v___x_4576_, 6);
v_messages_4584_ = lean_ctor_get(v___x_4576_, 7);
v_infoState_4585_ = lean_ctor_get(v___x_4576_, 8);
v_snapshotTasks_4586_ = lean_ctor_get(v___x_4576_, 9);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4588_ = v___x_4576_;
v_isShared_4589_ = v_isSharedCheck_4616_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_snapshotTasks_4586_);
lean_inc(v_infoState_4585_);
lean_inc(v_messages_4584_);
lean_inc(v_recordedDeps_4583_);
lean_inc(v_cache_4582_);
lean_inc(v_traceState_4577_);
lean_inc(v_auxDeclNGen_4581_);
lean_inc(v_ngen_4580_);
lean_inc(v_nextMacroScope_4579_);
lean_inc(v_env_4578_);
lean_dec(v___x_4576_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4616_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
uint64_t v_tid_4590_; lean_object* v_traces_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4615_; 
v_tid_4590_ = lean_ctor_get_uint64(v_traceState_4577_, sizeof(void*)*1);
v_traces_4591_ = lean_ctor_get(v_traceState_4577_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_traceState_4577_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4593_ = v_traceState_4577_;
v_isShared_4594_ = v_isSharedCheck_4615_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_traces_4591_);
lean_dec(v_traceState_4577_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4615_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; double v___x_4597_; uint8_t v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4595_ = lean_box(0);
v___x_4596_ = lean_box(0);
v___x_4597_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4598_ = 0;
v___x_4599_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4600_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4600_, 0, v_cls_4563_);
lean_ctor_set(v___x_4600_, 1, v___x_4596_);
lean_ctor_set(v___x_4600_, 2, v___x_4599_);
lean_ctor_set_float(v___x_4600_, sizeof(void*)*3, v___x_4597_);
lean_ctor_set_float(v___x_4600_, sizeof(void*)*3 + 8, v___x_4597_);
lean_ctor_set_uint8(v___x_4600_, sizeof(void*)*3 + 16, v___x_4598_);
v___x_4601_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4602_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4600_);
lean_ctor_set(v___x_4602_, 1, v_a_4572_);
lean_ctor_set(v___x_4602_, 2, v___x_4601_);
lean_inc(v_ref_4570_);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v_ref_4570_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
v___x_4604_ = l_Lean_PersistentArray_push___redArg(v_traces_4591_, v___x_4603_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4604_);
v___x_4606_ = v___x_4593_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4604_);
lean_ctor_set_uint64(v_reuseFailAlloc_4614_, sizeof(void*)*1, v_tid_4590_);
v___x_4606_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4608_; 
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 4, v___x_4606_);
v___x_4608_ = v___x_4588_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_env_4578_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v_nextMacroScope_4579_);
lean_ctor_set(v_reuseFailAlloc_4613_, 2, v_ngen_4580_);
lean_ctor_set(v_reuseFailAlloc_4613_, 3, v_auxDeclNGen_4581_);
lean_ctor_set(v_reuseFailAlloc_4613_, 4, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4613_, 5, v_cache_4582_);
lean_ctor_set(v_reuseFailAlloc_4613_, 6, v_recordedDeps_4583_);
lean_ctor_set(v_reuseFailAlloc_4613_, 7, v_messages_4584_);
lean_ctor_set(v_reuseFailAlloc_4613_, 8, v_infoState_4585_);
lean_ctor_set(v_reuseFailAlloc_4613_, 9, v_snapshotTasks_4586_);
v___x_4608_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4609_ = lean_st_ref_put(v___y_4568_, v___x_4608_);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v___x_4595_);
v___x_4611_ = v___x_4574_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4595_);
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
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0));
v___x_4628_ = l_Lean_stringToMessageData(v___x_4627_);
return v___x_4628_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2));
v___x_4631_ = l_Lean_stringToMessageData(v___x_4630_);
return v___x_4631_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4));
v___x_4634_ = l_Lean_stringToMessageData(v___x_4633_);
return v___x_4634_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6));
v___x_4637_ = l_Lean_stringToMessageData(v___x_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___x_4638_, lean_object* v_e_4639_, lean_object* v___x_4640_, lean_object* v___x_4641_, lean_object* v_cls_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
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
lean_object* v_toCold_4682_; lean_object* v_options_4683_; uint8_t v_hasTrace_4684_; 
v_toCold_4682_ = lean_ctor_get(v___y_4645_, 0);
v_options_4683_ = lean_ctor_get(v_toCold_4682_, 2);
v_hasTrace_4684_ = lean_ctor_get_uint8(v_options_4683_, sizeof(void*)*1);
if (v_hasTrace_4684_ == 0)
{
lean_dec(v_cls_4642_);
goto v___jp_4659_;
}
else
{
lean_object* v_inheritedTraceOptions_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v_inheritedTraceOptions_4685_ = lean_ctor_get(v_toCold_4682_, 11);
v___x_4686_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4642_);
v___x_4687_ = l_Lean_Name_append(v___x_4686_, v_cls_4642_);
v___x_4688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4685_, v_options_4683_, v___x_4687_);
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
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5);
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
lean_object* v_toCold_4702_; lean_object* v_options_4703_; uint8_t v_hasTrace_4704_; 
v_toCold_4702_ = lean_ctor_get(v___y_4645_, 0);
v_options_4703_ = lean_ctor_get(v_toCold_4702_, 2);
v_hasTrace_4704_ = lean_ctor_get_uint8(v_options_4703_, sizeof(void*)*1);
if (v_hasTrace_4704_ == 0)
{
lean_dec(v_cls_4642_);
goto v___jp_4659_;
}
else
{
lean_object* v_inheritedTraceOptions_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v_inheritedTraceOptions_4705_ = lean_ctor_get(v_toCold_4702_, 11);
v___x_4706_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4642_);
v___x_4707_ = l_Lean_Name_append(v___x_4706_, v_cls_4642_);
v___x_4708_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4705_, v_options_4703_, v___x_4707_);
lean_dec(v___x_4707_);
if (v___x_4708_ == 0)
{
lean_dec(v_cls_4642_);
goto v___jp_4659_;
}
else
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7);
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
v___x_4664_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1);
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
v___x_4670_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___x_4730_, lean_object* v_e_4731_, lean_object* v___x_4732_, lean_object* v___x_4733_, lean_object* v_cls_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___x_4730_, v_e_4731_, v___x_4732_, v___x_4733_, v_cls_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___x_4733_);
lean_dec(v___x_4732_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(uint8_t v___x_4741_, lean_object* v___f_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v___x_4794_; uint8_t v_beta_4795_; 
v___x_4794_ = l_Lean_Meta_Context_config(v___y_4743_);
v_beta_4795_ = lean_ctor_get_uint8(v___x_4794_, 13);
if (v_beta_4795_ == 0)
{
lean_dec_ref(v___x_4794_);
goto v___jp_4748_;
}
else
{
uint8_t v_iota_4796_; 
v_iota_4796_ = lean_ctor_get_uint8(v___x_4794_, 12);
if (v_iota_4796_ == 0)
{
lean_dec_ref(v___x_4794_);
goto v___jp_4748_;
}
else
{
uint8_t v_zeta_4797_; 
v_zeta_4797_ = lean_ctor_get_uint8(v___x_4794_, 15);
if (v_zeta_4797_ == 0)
{
lean_dec_ref(v___x_4794_);
goto v___jp_4748_;
}
else
{
uint8_t v_zetaHave_4798_; 
v_zetaHave_4798_ = lean_ctor_get_uint8(v___x_4794_, 18);
if (v_zetaHave_4798_ == 0)
{
lean_dec_ref(v___x_4794_);
goto v___jp_4748_;
}
else
{
uint8_t v_zetaDelta_4799_; 
v_zetaDelta_4799_ = lean_ctor_get_uint8(v___x_4794_, 16);
if (v_zetaDelta_4799_ == 0)
{
lean_dec_ref(v___x_4794_);
goto v___jp_4748_;
}
else
{
uint8_t v_etaStruct_4800_; uint8_t v_proj_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; 
v_etaStruct_4800_ = lean_ctor_get_uint8(v___x_4794_, 10);
v_proj_4801_ = lean_ctor_get_uint8(v___x_4794_, 14);
lean_dec_ref(v___x_4794_);
v___x_4802_ = lean_box(v_proj_4801_);
v___x_4803_ = lean_obj_tag_nat(v___x_4802_);
lean_dec(v___x_4802_);
v___x_4804_ = lean_unsigned_to_nat(2u);
v___x_4805_ = lean_nat_dec_eq(v___x_4803_, v___x_4804_);
if (v___x_4805_ == 0)
{
goto v___jp_4748_;
}
else
{
uint8_t v___x_4806_; uint8_t v___x_4807_; 
v___x_4806_ = 0;
v___x_4807_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4800_, v___x_4806_);
if (v___x_4807_ == 0)
{
goto v___jp_4748_;
}
else
{
lean_object* v___x_4808_; 
v___x_4808_ = lean_apply_5(v___f_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, lean_box(0));
return v___x_4808_;
}
}
}
}
}
}
}
v___jp_4748_:
{
lean_object* v___x_4749_; uint8_t v_foApprox_4750_; uint8_t v_ctxApprox_4751_; uint8_t v_quasiPatternApprox_4752_; uint8_t v_constApprox_4753_; uint8_t v_isDefEqStuckEx_4754_; uint8_t v_unificationHints_4755_; uint8_t v_proofIrrelevance_4756_; uint8_t v_assignSyntheticOpaque_4757_; uint8_t v_offsetCnstrs_4758_; uint8_t v_transparency_4759_; uint8_t v_univApprox_4760_; uint8_t v_zetaUnused_4761_; uint8_t v_canUnfoldPredicateConfig_4762_; uint8_t v_stringLitToCtor_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4793_; 
v___x_4749_ = l_Lean_Meta_Context_config(v___y_4743_);
v_foApprox_4750_ = lean_ctor_get_uint8(v___x_4749_, 0);
v_ctxApprox_4751_ = lean_ctor_get_uint8(v___x_4749_, 1);
v_quasiPatternApprox_4752_ = lean_ctor_get_uint8(v___x_4749_, 2);
v_constApprox_4753_ = lean_ctor_get_uint8(v___x_4749_, 3);
v_isDefEqStuckEx_4754_ = lean_ctor_get_uint8(v___x_4749_, 4);
v_unificationHints_4755_ = lean_ctor_get_uint8(v___x_4749_, 5);
v_proofIrrelevance_4756_ = lean_ctor_get_uint8(v___x_4749_, 6);
v_assignSyntheticOpaque_4757_ = lean_ctor_get_uint8(v___x_4749_, 7);
v_offsetCnstrs_4758_ = lean_ctor_get_uint8(v___x_4749_, 8);
v_transparency_4759_ = lean_ctor_get_uint8(v___x_4749_, 9);
v_univApprox_4760_ = lean_ctor_get_uint8(v___x_4749_, 11);
v_zetaUnused_4761_ = lean_ctor_get_uint8(v___x_4749_, 17);
v_canUnfoldPredicateConfig_4762_ = lean_ctor_get_uint8(v___x_4749_, 19);
v_stringLitToCtor_4763_ = lean_ctor_get_uint8(v___x_4749_, 20);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4765_ = v___x_4749_;
v_isShared_4766_ = v_isSharedCheck_4793_;
goto v_resetjp_4764_;
}
else
{
lean_dec(v___x_4749_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4793_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
uint8_t v___x_4767_; uint8_t v___x_4768_; lean_object* v___x_4770_; 
v___x_4767_ = 0;
v___x_4768_ = 2;
if (v_isShared_4766_ == 0)
{
v___x_4770_ = v___x_4765_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 0, v_foApprox_4750_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 1, v_ctxApprox_4751_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 2, v_quasiPatternApprox_4752_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 3, v_constApprox_4753_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 4, v_isDefEqStuckEx_4754_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 5, v_unificationHints_4755_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 6, v_proofIrrelevance_4756_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 7, v_assignSyntheticOpaque_4757_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 8, v_offsetCnstrs_4758_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 9, v_transparency_4759_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 11, v_univApprox_4760_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 17, v_zetaUnused_4761_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 19, v_canUnfoldPredicateConfig_4762_);
lean_ctor_set_uint8(v_reuseFailAlloc_4792_, 20, v_stringLitToCtor_4763_);
v___x_4770_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
uint8_t v_trackZetaDelta_4771_; lean_object* v_zetaDeltaSet_4772_; lean_object* v_lctx_4773_; lean_object* v_localInstances_4774_; lean_object* v_defEqCtx_x3f_4775_; lean_object* v_synthPendingDepth_4776_; lean_object* v_customCanUnfoldPredicate_x3f_4777_; uint8_t v_univApprox_4778_; uint8_t v_inTypeClassResolution_4779_; uint8_t v_cacheInferType_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4790_; 
lean_ctor_set_uint8(v___x_4770_, 10, v___x_4767_);
lean_ctor_set_uint8(v___x_4770_, 12, v___x_4741_);
lean_ctor_set_uint8(v___x_4770_, 13, v___x_4741_);
lean_ctor_set_uint8(v___x_4770_, 14, v___x_4768_);
lean_ctor_set_uint8(v___x_4770_, 15, v___x_4741_);
lean_ctor_set_uint8(v___x_4770_, 16, v___x_4741_);
lean_ctor_set_uint8(v___x_4770_, 18, v___x_4741_);
v_trackZetaDelta_4771_ = lean_ctor_get_uint8(v___y_4743_, sizeof(void*)*7);
v_zetaDeltaSet_4772_ = lean_ctor_get(v___y_4743_, 1);
v_lctx_4773_ = lean_ctor_get(v___y_4743_, 2);
v_localInstances_4774_ = lean_ctor_get(v___y_4743_, 3);
v_defEqCtx_x3f_4775_ = lean_ctor_get(v___y_4743_, 4);
v_synthPendingDepth_4776_ = lean_ctor_get(v___y_4743_, 5);
v_customCanUnfoldPredicate_x3f_4777_ = lean_ctor_get(v___y_4743_, 6);
v_univApprox_4778_ = lean_ctor_get_uint8(v___y_4743_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4779_ = lean_ctor_get_uint8(v___y_4743_, sizeof(void*)*7 + 2);
v_cacheInferType_4780_ = lean_ctor_get_uint8(v___y_4743_, sizeof(void*)*7 + 3);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___y_4743_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; 
v_unused_4791_ = lean_ctor_get(v___y_4743_, 0);
lean_dec(v_unused_4791_);
v___x_4782_ = v___y_4743_;
v_isShared_4783_ = v_isSharedCheck_4790_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4777_);
lean_inc(v_synthPendingDepth_4776_);
lean_inc(v_defEqCtx_x3f_4775_);
lean_inc(v_localInstances_4774_);
lean_inc(v_lctx_4773_);
lean_inc(v_zetaDeltaSet_4772_);
lean_dec(v___y_4743_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4790_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
uint64_t v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4787_; 
v___x_4784_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4770_);
v___x_4785_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4785_, 0, v___x_4770_);
lean_ctor_set_uint64(v___x_4785_, sizeof(void*)*1, v___x_4784_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4785_);
v___x_4787_ = v___x_4782_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_zetaDeltaSet_4772_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_lctx_4773_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_localInstances_4774_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_defEqCtx_x3f_4775_);
lean_ctor_set(v_reuseFailAlloc_4789_, 5, v_synthPendingDepth_4776_);
lean_ctor_set(v_reuseFailAlloc_4789_, 6, v_customCanUnfoldPredicate_x3f_4777_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*7, v_trackZetaDelta_4771_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*7 + 1, v_univApprox_4778_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4779_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*7 + 3, v_cacheInferType_4780_);
v___x_4787_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
lean_object* v___x_4788_; 
v___x_4788_ = lean_apply_5(v___f_4742_, v___x_4787_, v___y_4744_, v___y_4745_, v___y_4746_, lean_box(0));
return v___x_4788_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4809_, lean_object* v___f_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
uint8_t v___x_14191__boxed_4816_; lean_object* v_res_4817_; 
v___x_14191__boxed_4816_ = lean_unbox(v___x_4809_);
v_res_4817_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_14191__boxed_4816_, v___f_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4818_, lean_object* v_cache_4819_, lean_object* v_a_x3f_4820_){
_start:
{
lean_object* v___x_4822_; lean_object* v_mctx_4823_; lean_object* v_zetaDeltaFVarIds_4824_; lean_object* v_postponed_4825_; lean_object* v_diag_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4836_; 
v___x_4822_ = lean_st_ref_take(v___y_4818_);
v_mctx_4823_ = lean_ctor_get(v___x_4822_, 0);
v_zetaDeltaFVarIds_4824_ = lean_ctor_get(v___x_4822_, 2);
v_postponed_4825_ = lean_ctor_get(v___x_4822_, 3);
v_diag_4826_ = lean_ctor_get(v___x_4822_, 4);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4836_ == 0)
{
lean_object* v_unused_4837_; 
v_unused_4837_ = lean_ctor_get(v___x_4822_, 1);
lean_dec(v_unused_4837_);
v___x_4828_ = v___x_4822_;
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_diag_4826_);
lean_inc(v_postponed_4825_);
lean_inc(v_zetaDeltaFVarIds_4824_);
lean_inc(v_mctx_4823_);
lean_dec(v___x_4822_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4830_; lean_object* v___x_4832_; 
v___x_4830_ = lean_box(0);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 1, v_cache_4819_);
v___x_4832_ = v___x_4828_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_mctx_4823_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_cache_4819_);
lean_ctor_set(v_reuseFailAlloc_4835_, 2, v_zetaDeltaFVarIds_4824_);
lean_ctor_set(v_reuseFailAlloc_4835_, 3, v_postponed_4825_);
lean_ctor_set(v_reuseFailAlloc_4835_, 4, v_diag_4826_);
v___x_4832_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = lean_st_ref_put(v___y_4818_, v___x_4832_);
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4830_);
return v___x_4834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4838_, lean_object* v_cache_4839_, lean_object* v_a_x3f_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4838_, v_cache_4839_, v_a_x3f_4840_);
lean_dec(v_a_x3f_4840_);
lean_dec(v___y_4838_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(lean_object* v___y_4843_, lean_object* v_zetaDeltaFVarIds_4844_, lean_object* v_a_x3f_4845_){
_start:
{
lean_object* v___x_4847_; lean_object* v_mctx_4848_; lean_object* v_cache_4849_; lean_object* v_postponed_4850_; lean_object* v_diag_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4861_; 
v___x_4847_ = lean_st_ref_take(v___y_4843_);
v_mctx_4848_ = lean_ctor_get(v___x_4847_, 0);
v_cache_4849_ = lean_ctor_get(v___x_4847_, 1);
v_postponed_4850_ = lean_ctor_get(v___x_4847_, 3);
v_diag_4851_ = lean_ctor_get(v___x_4847_, 4);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4861_ == 0)
{
lean_object* v_unused_4862_; 
v_unused_4862_ = lean_ctor_get(v___x_4847_, 2);
lean_dec(v_unused_4862_);
v___x_4853_ = v___x_4847_;
v_isShared_4854_ = v_isSharedCheck_4861_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_diag_4851_);
lean_inc(v_postponed_4850_);
lean_inc(v_cache_4849_);
lean_inc(v_mctx_4848_);
lean_dec(v___x_4847_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4861_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4855_; lean_object* v___x_4857_; 
v___x_4855_ = lean_box(0);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 2, v_zetaDeltaFVarIds_4844_);
v___x_4857_ = v___x_4853_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_mctx_4848_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_cache_4849_);
lean_ctor_set(v_reuseFailAlloc_4860_, 2, v_zetaDeltaFVarIds_4844_);
lean_ctor_set(v_reuseFailAlloc_4860_, 3, v_postponed_4850_);
lean_ctor_set(v_reuseFailAlloc_4860_, 4, v_diag_4851_);
v___x_4857_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4858_ = lean_st_ref_put(v___y_4843_, v___x_4857_);
v___x_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4855_);
return v___x_4859_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___y_4863_, lean_object* v_zetaDeltaFVarIds_4864_, lean_object* v_a_x3f_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4863_, v_zetaDeltaFVarIds_4864_, v_a_x3f_4865_);
lean_dec(v_a_x3f_4865_);
lean_dec(v___y_4863_);
return v_res_4867_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg(){
_start:
{
lean_object* v___x_4871_; 
v___x_4871_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___closed__0);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg___boxed(lean_object* v___dummy_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg();
return v_res_4873_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1));
v___x_4878_ = l_Lean_MessageData_ofFormat(v___x_4877_);
return v___x_4878_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4879_ = lean_box(0);
v___x_4880_ = lean_unsigned_to_nat(16u);
v___x_4881_ = lean_mk_array(v___x_4880_, v___x_4879_);
return v___x_4881_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4882_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4883_);
lean_ctor_set(v___x_4884_, 1, v___x_4882_);
return v___x_4884_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4885_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4886_ = lean_unsigned_to_nat(0u);
v___x_4887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v___x_4885_);
return v___x_4887_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6(void){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1___redArg();
return v___x_4888_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7(void){
_start:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
return v___x_4890_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8(void){
_start:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4891_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7);
v___x_4892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4891_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
return v___x_4892_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__9(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = lean_unsigned_to_nat(0u);
v___x_4894_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7);
v___x_4895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4894_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
lean_ctor_set(v___x_4895_, 2, v___x_4893_);
return v___x_4895_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__10(void){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4896_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__9, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__9_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__9);
v___x_4897_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__8);
v___x_4898_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__7);
v___x_4899_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
v___x_4900_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4899_);
lean_ctor_set(v___x_4900_, 1, v___x_4898_);
lean_ctor_set(v___x_4900_, 2, v___x_4897_);
lean_ctor_set(v___x_4900_, 3, v___x_4898_);
lean_ctor_set(v___x_4900_, 4, v___x_4898_);
lean_ctor_set(v___x_4900_, 5, v___x_4898_);
lean_ctor_set(v___x_4900_, 6, v___x_4896_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_4901_, lean_object* v_e_4902_, lean_object* v_cls_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
if (v___x_4901_ == 0)
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_dec(v_cls_4903_);
v___x_4909_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_4910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4910_, 0, v_e_4902_);
lean_ctor_set(v___x_4910_, 1, v___x_4909_);
v___x_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
return v___x_4911_;
}
else
{
uint8_t v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___f_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v_cache_4919_; lean_object* v_a_4921_; lean_object* v___x_4932_; lean_object* v_mctx_4933_; lean_object* v_zetaDeltaFVarIds_4934_; lean_object* v_postponed_4935_; lean_object* v_diag_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_5014_; 
v___x_4912_ = 0;
v___x_4913_ = lean_box(0);
v___x_4914_ = lean_unsigned_to_nat(0u);
v___x_4915_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
v___f_4916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4916_, 0, v___x_4915_);
lean_closure_set(v___f_4916_, 1, v_e_4902_);
lean_closure_set(v___f_4916_, 2, v___x_4913_);
lean_closure_set(v___f_4916_, 3, v___x_4914_);
lean_closure_set(v___f_4916_, 4, v_cls_4903_);
v___x_4917_ = lean_box(1);
v___x_4918_ = lean_st_ref_get(v___y_4905_);
v_cache_4919_ = lean_ctor_get(v___x_4918_, 1);
lean_inc_ref(v_cache_4919_);
lean_dec(v___x_4918_);
v___x_4932_ = lean_st_ref_take(v___y_4905_);
v_mctx_4933_ = lean_ctor_get(v___x_4932_, 0);
v_zetaDeltaFVarIds_4934_ = lean_ctor_get(v___x_4932_, 2);
v_postponed_4935_ = lean_ctor_get(v___x_4932_, 3);
v_diag_4936_ = lean_ctor_get(v___x_4932_, 4);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_5014_ == 0)
{
lean_object* v_unused_5015_; 
v_unused_5015_ = lean_ctor_get(v___x_4932_, 1);
lean_dec(v_unused_5015_);
v___x_4938_ = v___x_4932_;
v_isShared_4939_ = v_isSharedCheck_5014_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_diag_4936_);
lean_inc(v_postponed_4935_);
lean_inc(v_zetaDeltaFVarIds_4934_);
lean_inc(v_mctx_4933_);
lean_dec(v___x_4932_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_5014_;
goto v_resetjp_4937_;
}
v___jp_4920_:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
v___x_4922_ = lean_box(0);
v___x_4923_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4905_, v_cache_4919_, v___x_4922_);
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
lean_ctor_set_tag(v___x_4925_, 1);
lean_ctor_set(v___x_4925_, 0, v_a_4921_);
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4921_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
v_resetjp_4937_:
{
lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4940_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__10);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 1, v___x_4940_);
v___x_4942_ = v___x_4938_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_mctx_4933_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v___x_4940_);
lean_ctor_set(v_reuseFailAlloc_5013_, 2, v_zetaDeltaFVarIds_4934_);
lean_ctor_set(v_reuseFailAlloc_5013_, 3, v_postponed_4935_);
lean_ctor_set(v_reuseFailAlloc_5013_, 4, v_diag_4936_);
v___x_4942_ = v_reuseFailAlloc_5013_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4943_; lean_object* v_keyedConfig_4944_; lean_object* v_zetaDeltaSet_4945_; lean_object* v_lctx_4946_; lean_object* v_localInstances_4947_; lean_object* v_defEqCtx_x3f_4948_; lean_object* v_synthPendingDepth_4949_; lean_object* v_customCanUnfoldPredicate_x3f_4950_; uint8_t v_univApprox_4951_; uint8_t v_inTypeClassResolution_4952_; uint8_t v_cacheInferType_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v_mctx_4956_; lean_object* v_cache_4957_; lean_object* v_zetaDeltaFVarIds_4958_; lean_object* v_postponed_4959_; lean_object* v_diag_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_5012_; 
v___x_4943_ = lean_st_ref_put(v___y_4905_, v___x_4942_);
v_keyedConfig_4944_ = lean_ctor_get(v___y_4904_, 0);
v_zetaDeltaSet_4945_ = lean_ctor_get(v___y_4904_, 1);
v_lctx_4946_ = lean_ctor_get(v___y_4904_, 2);
v_localInstances_4947_ = lean_ctor_get(v___y_4904_, 3);
v_defEqCtx_x3f_4948_ = lean_ctor_get(v___y_4904_, 4);
v_synthPendingDepth_4949_ = lean_ctor_get(v___y_4904_, 5);
v_customCanUnfoldPredicate_x3f_4950_ = lean_ctor_get(v___y_4904_, 6);
v_univApprox_4951_ = lean_ctor_get_uint8(v___y_4904_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4952_ = lean_ctor_get_uint8(v___y_4904_, sizeof(void*)*7 + 2);
v_cacheInferType_4953_ = lean_ctor_get_uint8(v___y_4904_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_4950_);
lean_inc(v_synthPendingDepth_4949_);
lean_inc(v_defEqCtx_x3f_4948_);
lean_inc_ref(v_localInstances_4947_);
lean_inc_ref(v_lctx_4946_);
lean_inc(v_zetaDeltaSet_4945_);
lean_inc_ref(v_keyedConfig_4944_);
v___x_4954_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4954_, 0, v_keyedConfig_4944_);
lean_ctor_set(v___x_4954_, 1, v_zetaDeltaSet_4945_);
lean_ctor_set(v___x_4954_, 2, v_lctx_4946_);
lean_ctor_set(v___x_4954_, 3, v_localInstances_4947_);
lean_ctor_set(v___x_4954_, 4, v_defEqCtx_x3f_4948_);
lean_ctor_set(v___x_4954_, 5, v_synthPendingDepth_4949_);
lean_ctor_set(v___x_4954_, 6, v_customCanUnfoldPredicate_x3f_4950_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7, v___x_4901_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7 + 1, v_univApprox_4951_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4952_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7 + 3, v_cacheInferType_4953_);
v___x_4955_ = lean_st_ref_take(v___y_4905_);
v_mctx_4956_ = lean_ctor_get(v___x_4955_, 0);
v_cache_4957_ = lean_ctor_get(v___x_4955_, 1);
v_zetaDeltaFVarIds_4958_ = lean_ctor_get(v___x_4955_, 2);
v_postponed_4959_ = lean_ctor_get(v___x_4955_, 3);
v_diag_4960_ = lean_ctor_get(v___x_4955_, 4);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_4962_ = v___x_4955_;
v_isShared_4963_ = v_isSharedCheck_5012_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_diag_4960_);
lean_inc(v_postponed_4959_);
lean_inc(v_zetaDeltaFVarIds_4958_);
lean_inc(v_cache_4957_);
lean_inc(v_mctx_4956_);
lean_dec(v___x_4955_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_5012_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v_a_4965_; lean_object* v_a_4969_; lean_object* v___y_4982_; lean_object* v___y_4986_; lean_object* v___x_4990_; 
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 2, v___x_4917_);
v___x_4990_ = v___x_4962_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_mctx_4956_);
lean_ctor_set(v_reuseFailAlloc_5011_, 1, v_cache_4957_);
lean_ctor_set(v_reuseFailAlloc_5011_, 2, v___x_4917_);
lean_ctor_set(v_reuseFailAlloc_5011_, 3, v_postponed_4959_);
lean_ctor_set(v_reuseFailAlloc_5011_, 4, v_diag_4960_);
v___x_4990_ = v_reuseFailAlloc_5011_;
goto v_reusejp_4989_;
}
v___jp_4964_:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = lean_box(0);
v___x_4967_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4905_, v_zetaDeltaFVarIds_4958_, v___x_4966_);
lean_dec_ref(v___x_4967_);
v_a_4921_ = v_a_4965_;
goto v___jp_4920_;
}
v___jp_4968_:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4979_; 
lean_inc(v_a_4969_);
v___x_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4970_, 0, v_a_4969_);
v___x_4971_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4905_, v_zetaDeltaFVarIds_4958_, v___x_4970_);
lean_dec_ref(v___x_4971_);
v___x_4972_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4905_, v_cache_4919_, v___x_4970_);
lean_dec_ref_known(v___x_4970_, 1);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4979_ == 0)
{
lean_object* v_unused_4980_; 
v_unused_4980_ = lean_ctor_get(v___x_4972_, 0);
lean_dec(v_unused_4980_);
v___x_4974_ = v___x_4972_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_dec(v___x_4972_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v_a_4969_);
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4969_);
v___x_4977_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
return v___x_4977_;
}
}
}
v___jp_4981_:
{
if (lean_obj_tag(v___y_4982_) == 0)
{
lean_object* v_a_4983_; 
v_a_4983_ = lean_ctor_get(v___y_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___y_4982_, 1);
v_a_4969_ = v_a_4983_;
goto v___jp_4968_;
}
else
{
lean_object* v_a_4984_; 
v_a_4984_ = lean_ctor_get(v___y_4982_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___y_4982_, 1);
v_a_4965_ = v_a_4984_;
goto v___jp_4964_;
}
}
v___jp_4985_:
{
if (lean_obj_tag(v___y_4986_) == 0)
{
lean_object* v_a_4987_; 
v_a_4987_ = lean_ctor_get(v___y_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___y_4986_, 1);
v_a_4969_ = v_a_4987_;
goto v___jp_4968_;
}
else
{
lean_object* v_a_4988_; 
v_a_4988_ = lean_ctor_get(v___y_4986_, 0);
lean_inc(v_a_4988_);
lean_dec_ref_known(v___y_4986_, 1);
v_a_4965_ = v_a_4988_;
goto v___jp_4964_;
}
}
v_reusejp_4989_:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; uint8_t v_transparency_4993_; uint8_t v___x_4994_; 
v___x_4991_ = lean_st_ref_put(v___y_4905_, v___x_4990_);
v___x_4992_ = l_Lean_Meta_Context_config(v___x_4954_);
v_transparency_4993_ = lean_ctor_get_uint8(v___x_4992_, 9);
lean_dec_ref(v___x_4992_);
v___x_4994_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4993_, v___x_4912_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; uint8_t v_transparency_4998_; uint8_t v___x_4999_; uint8_t v___x_5000_; 
lean_dec_ref_known(v___x_4954_, 7);
lean_inc_ref(v_keyedConfig_4944_);
v___x_4995_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4912_, v_keyedConfig_4944_);
lean_inc(v_customCanUnfoldPredicate_x3f_4950_);
lean_inc(v_synthPendingDepth_4949_);
lean_inc(v_defEqCtx_x3f_4948_);
lean_inc_ref(v_localInstances_4947_);
lean_inc_ref(v_lctx_4946_);
lean_inc(v_zetaDeltaSet_4945_);
lean_inc_ref(v___x_4995_);
v___x_4996_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
lean_ctor_set(v___x_4996_, 1, v_zetaDeltaSet_4945_);
lean_ctor_set(v___x_4996_, 2, v_lctx_4946_);
lean_ctor_set(v___x_4996_, 3, v_localInstances_4947_);
lean_ctor_set(v___x_4996_, 4, v_defEqCtx_x3f_4948_);
lean_ctor_set(v___x_4996_, 5, v_synthPendingDepth_4949_);
lean_ctor_set(v___x_4996_, 6, v_customCanUnfoldPredicate_x3f_4950_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7, v___x_4901_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7 + 1, v_univApprox_4951_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4952_);
lean_ctor_set_uint8(v___x_4996_, sizeof(void*)*7 + 3, v_cacheInferType_4953_);
v___x_4997_ = l_Lean_Meta_Context_config(v___x_4996_);
v_transparency_4998_ = lean_ctor_get_uint8(v___x_4997_, 9);
lean_dec_ref(v___x_4997_);
v___x_4999_ = 1;
v___x_5000_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4998_, v___x_4999_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; 
lean_dec_ref(v___x_4995_);
lean_inc(v___y_4907_);
lean_inc_ref(v___y_4906_);
lean_inc(v___y_4905_);
v___x_5001_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4901_, v___f_4916_, v___x_4996_, v___y_4905_, v___y_4906_, v___y_4907_);
v___y_4982_ = v___x_5001_;
goto v___jp_4981_;
}
else
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
lean_dec_ref_known(v___x_4996_, 7);
v___x_5002_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4999_, v___x_4995_);
lean_inc(v_customCanUnfoldPredicate_x3f_4950_);
lean_inc(v_synthPendingDepth_4949_);
lean_inc(v_defEqCtx_x3f_4948_);
lean_inc_ref(v_localInstances_4947_);
lean_inc_ref(v_lctx_4946_);
lean_inc(v_zetaDeltaSet_4945_);
v___x_5003_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5003_, 0, v___x_5002_);
lean_ctor_set(v___x_5003_, 1, v_zetaDeltaSet_4945_);
lean_ctor_set(v___x_5003_, 2, v_lctx_4946_);
lean_ctor_set(v___x_5003_, 3, v_localInstances_4947_);
lean_ctor_set(v___x_5003_, 4, v_defEqCtx_x3f_4948_);
lean_ctor_set(v___x_5003_, 5, v_synthPendingDepth_4949_);
lean_ctor_set(v___x_5003_, 6, v_customCanUnfoldPredicate_x3f_4950_);
lean_ctor_set_uint8(v___x_5003_, sizeof(void*)*7, v___x_4901_);
lean_ctor_set_uint8(v___x_5003_, sizeof(void*)*7 + 1, v_univApprox_4951_);
lean_ctor_set_uint8(v___x_5003_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4952_);
lean_ctor_set_uint8(v___x_5003_, sizeof(void*)*7 + 3, v_cacheInferType_4953_);
lean_inc(v___y_4907_);
lean_inc_ref(v___y_4906_);
lean_inc(v___y_4905_);
v___x_5004_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4901_, v___f_4916_, v___x_5003_, v___y_4905_, v___y_4906_, v___y_4907_);
v___y_4982_ = v___x_5004_;
goto v___jp_4981_;
}
}
else
{
uint8_t v___x_5005_; uint8_t v___x_5006_; 
v___x_5005_ = 1;
v___x_5006_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4993_, v___x_5005_);
if (v___x_5006_ == 0)
{
lean_object* v___x_5007_; 
lean_inc(v___y_4907_);
lean_inc_ref(v___y_4906_);
lean_inc(v___y_4905_);
v___x_5007_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4994_, v___f_4916_, v___x_4954_, v___y_4905_, v___y_4906_, v___y_4907_);
v___y_4986_ = v___x_5007_;
goto v___jp_4985_;
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_dec_ref_known(v___x_4954_, 7);
lean_inc_ref(v_keyedConfig_4944_);
v___x_5008_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_5005_, v_keyedConfig_4944_);
lean_inc(v_customCanUnfoldPredicate_x3f_4950_);
lean_inc(v_synthPendingDepth_4949_);
lean_inc(v_defEqCtx_x3f_4948_);
lean_inc_ref(v_localInstances_4947_);
lean_inc_ref(v_lctx_4946_);
lean_inc(v_zetaDeltaSet_4945_);
v___x_5009_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5009_, 0, v___x_5008_);
lean_ctor_set(v___x_5009_, 1, v_zetaDeltaSet_4945_);
lean_ctor_set(v___x_5009_, 2, v_lctx_4946_);
lean_ctor_set(v___x_5009_, 3, v_localInstances_4947_);
lean_ctor_set(v___x_5009_, 4, v_defEqCtx_x3f_4948_);
lean_ctor_set(v___x_5009_, 5, v_synthPendingDepth_4949_);
lean_ctor_set(v___x_5009_, 6, v_customCanUnfoldPredicate_x3f_4950_);
lean_ctor_set_uint8(v___x_5009_, sizeof(void*)*7, v___x_4901_);
lean_ctor_set_uint8(v___x_5009_, sizeof(void*)*7 + 1, v_univApprox_4951_);
lean_ctor_set_uint8(v___x_5009_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4952_);
lean_ctor_set_uint8(v___x_5009_, sizeof(void*)*7 + 3, v_cacheInferType_4953_);
lean_inc(v___y_4907_);
lean_inc_ref(v___y_4906_);
lean_inc(v___y_4905_);
v___x_5010_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4994_, v___f_4916_, v___x_5009_, v___y_4905_, v___y_4906_, v___y_4907_);
v___y_4986_ = v___x_5010_;
goto v___jp_4985_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_5016_, lean_object* v_e_5017_, lean_object* v_cls_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
uint8_t v___x_14406__boxed_5024_; lean_object* v_res_5025_; 
v___x_14406__boxed_5024_ = lean_unbox(v___x_5016_);
v_res_5025_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14406__boxed_5024_, v_e_5017_, v_cls_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
if (lean_obj_tag(v_x_5026_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5040_; 
v_a_5032_ = lean_ctor_get(v_x_5026_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v_x_5026_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5034_ = v_x_5026_;
v_isShared_5035_ = v_isSharedCheck_5040_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v_x_5026_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5040_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5036_; lean_object* v___x_5038_; 
v___x_5036_ = l_Lean_Exception_toMessageData(v_a_5032_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5036_);
v___x_5038_ = v___x_5034_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5036_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5049_; 
v_a_5041_ = lean_ctor_get(v_x_5026_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v_x_5026_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5043_ = v_x_5026_;
v_isShared_5044_ = v_isSharedCheck_5049_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v_x_5026_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5049_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v_snd_5045_; lean_object* v___x_5047_; 
v_snd_5045_ = lean_ctor_get(v_a_5041_, 1);
lean_inc(v_snd_5045_);
lean_dec(v_a_5041_);
if (v_isShared_5044_ == 0)
{
lean_ctor_set_tag(v___x_5043_, 0);
lean_ctor_set(v___x_5043_, 0, v_snd_5045_);
v___x_5047_ = v___x_5043_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_snd_5045_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(lean_object* v_oldTraces_5057_, lean_object* v_data_5058_, lean_object* v_ref_5059_, lean_object* v_msg_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
lean_object* v_toCold_5066_; lean_object* v_currRecDepth_5067_; lean_object* v_ref_5068_; uint16_t v_optionFlags_5069_; uint8_t v_suppressElabErrors_5070_; uint8_t v_checkDeprecated_5071_; uint8_t v_isRecordingDeps_5072_; lean_object* v_ref_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v_traceState_5076_; lean_object* v_traces_5077_; lean_object* v___x_5078_; size_t v_sz_5079_; size_t v___x_5080_; lean_object* v___x_5081_; lean_object* v_msg_5082_; lean_object* v___x_5083_; lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5122_; 
v_toCold_5066_ = lean_ctor_get(v___y_5063_, 0);
v_currRecDepth_5067_ = lean_ctor_get(v___y_5063_, 1);
v_ref_5068_ = lean_ctor_get(v___y_5063_, 2);
v_optionFlags_5069_ = lean_ctor_get_uint16(v___y_5063_, sizeof(void*)*3);
v_suppressElabErrors_5070_ = lean_ctor_get_uint8(v___y_5063_, sizeof(void*)*3 + 2);
v_checkDeprecated_5071_ = lean_ctor_get_uint8(v___y_5063_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5072_ = lean_ctor_get_uint8(v___y_5063_, sizeof(void*)*3 + 4);
v_ref_5073_ = l_Lean_replaceRef(v_ref_5059_, v_ref_5068_);
lean_inc(v_currRecDepth_5067_);
lean_inc_ref(v_toCold_5066_);
v___x_5074_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5074_, 0, v_toCold_5066_);
lean_ctor_set(v___x_5074_, 1, v_currRecDepth_5067_);
lean_ctor_set(v___x_5074_, 2, v_ref_5073_);
lean_ctor_set_uint16(v___x_5074_, sizeof(void*)*3, v_optionFlags_5069_);
lean_ctor_set_uint8(v___x_5074_, sizeof(void*)*3 + 2, v_suppressElabErrors_5070_);
lean_ctor_set_uint8(v___x_5074_, sizeof(void*)*3 + 3, v_checkDeprecated_5071_);
lean_ctor_set_uint8(v___x_5074_, sizeof(void*)*3 + 4, v_isRecordingDeps_5072_);
v___x_5075_ = lean_st_ref_get(v___y_5064_);
v_traceState_5076_ = lean_ctor_get(v___x_5075_, 4);
lean_inc_ref(v_traceState_5076_);
lean_dec(v___x_5075_);
v_traces_5077_ = lean_ctor_get(v_traceState_5076_, 0);
lean_inc_ref(v_traces_5077_);
lean_dec_ref(v_traceState_5076_);
v___x_5078_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5077_);
lean_dec_ref(v_traces_5077_);
v_sz_5079_ = lean_array_size(v___x_5078_);
v___x_5080_ = ((size_t)0ULL);
v___x_5081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5079_, v___x_5080_, v___x_5078_);
v_msg_5082_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5082_, 0, v_data_5058_);
lean_ctor_set(v_msg_5082_, 1, v_msg_5060_);
lean_ctor_set(v_msg_5082_, 2, v___x_5081_);
v___x_5083_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5082_, v___y_5061_, v___y_5062_, v___x_5074_, v___y_5064_);
lean_dec_ref_known(v___x_5074_, 3);
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5086_ = v___x_5083_;
v_isShared_5087_ = v_isSharedCheck_5122_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5083_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5122_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5088_; lean_object* v_traceState_5089_; lean_object* v_env_5090_; lean_object* v_nextMacroScope_5091_; lean_object* v_ngen_5092_; lean_object* v_auxDeclNGen_5093_; lean_object* v_cache_5094_; lean_object* v_recordedDeps_5095_; lean_object* v_messages_5096_; lean_object* v_infoState_5097_; lean_object* v_snapshotTasks_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5121_; 
v___x_5088_ = lean_st_ref_take(v___y_5064_);
v_traceState_5089_ = lean_ctor_get(v___x_5088_, 4);
v_env_5090_ = lean_ctor_get(v___x_5088_, 0);
v_nextMacroScope_5091_ = lean_ctor_get(v___x_5088_, 1);
v_ngen_5092_ = lean_ctor_get(v___x_5088_, 2);
v_auxDeclNGen_5093_ = lean_ctor_get(v___x_5088_, 3);
v_cache_5094_ = lean_ctor_get(v___x_5088_, 5);
v_recordedDeps_5095_ = lean_ctor_get(v___x_5088_, 6);
v_messages_5096_ = lean_ctor_get(v___x_5088_, 7);
v_infoState_5097_ = lean_ctor_get(v___x_5088_, 8);
v_snapshotTasks_5098_ = lean_ctor_get(v___x_5088_, 9);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5100_ = v___x_5088_;
v_isShared_5101_ = v_isSharedCheck_5121_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_snapshotTasks_5098_);
lean_inc(v_infoState_5097_);
lean_inc(v_messages_5096_);
lean_inc(v_recordedDeps_5095_);
lean_inc(v_cache_5094_);
lean_inc(v_traceState_5089_);
lean_inc(v_auxDeclNGen_5093_);
lean_inc(v_ngen_5092_);
lean_inc(v_nextMacroScope_5091_);
lean_inc(v_env_5090_);
lean_dec(v___x_5088_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5121_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
uint64_t v_tid_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5119_; 
v_tid_5102_ = lean_ctor_get_uint64(v_traceState_5089_, sizeof(void*)*1);
v_isSharedCheck_5119_ = !lean_is_exclusive(v_traceState_5089_);
if (v_isSharedCheck_5119_ == 0)
{
lean_object* v_unused_5120_; 
v_unused_5120_ = lean_ctor_get(v_traceState_5089_, 0);
lean_dec(v_unused_5120_);
v___x_5104_ = v_traceState_5089_;
v_isShared_5105_ = v_isSharedCheck_5119_;
goto v_resetjp_5103_;
}
else
{
lean_dec(v_traceState_5089_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5119_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5110_; 
v___x_5106_ = lean_box(0);
v___x_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5107_, 0, v_ref_5059_);
lean_ctor_set(v___x_5107_, 1, v_a_5084_);
v___x_5108_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5057_, v___x_5107_);
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 0, v___x_5108_);
v___x_5110_ = v___x_5104_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5108_);
lean_ctor_set_uint64(v_reuseFailAlloc_5118_, sizeof(void*)*1, v_tid_5102_);
v___x_5110_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
lean_object* v___x_5112_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v___x_5110_);
v___x_5112_ = v___x_5100_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_env_5090_);
lean_ctor_set(v_reuseFailAlloc_5117_, 1, v_nextMacroScope_5091_);
lean_ctor_set(v_reuseFailAlloc_5117_, 2, v_ngen_5092_);
lean_ctor_set(v_reuseFailAlloc_5117_, 3, v_auxDeclNGen_5093_);
lean_ctor_set(v_reuseFailAlloc_5117_, 4, v___x_5110_);
lean_ctor_set(v_reuseFailAlloc_5117_, 5, v_cache_5094_);
lean_ctor_set(v_reuseFailAlloc_5117_, 6, v_recordedDeps_5095_);
lean_ctor_set(v_reuseFailAlloc_5117_, 7, v_messages_5096_);
lean_ctor_set(v_reuseFailAlloc_5117_, 8, v_infoState_5097_);
lean_ctor_set(v_reuseFailAlloc_5117_, 9, v_snapshotTasks_5098_);
v___x_5112_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
lean_object* v___x_5113_; lean_object* v___x_5115_; 
v___x_5113_ = lean_st_ref_put(v___y_5064_, v___x_5112_);
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 0, v___x_5106_);
v___x_5115_ = v___x_5086_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5106_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4___boxed(lean_object* v_oldTraces_5123_, lean_object* v_data_5124_, lean_object* v_ref_5125_, lean_object* v_msg_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(v_oldTraces_5123_, v_data_5124_, v_ref_5125_, v_msg_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
return v_res_5132_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6(lean_object* v_e_5133_){
_start:
{
if (lean_obj_tag(v_e_5133_) == 0)
{
uint8_t v___x_5134_; 
v___x_5134_ = 2;
return v___x_5134_;
}
else
{
uint8_t v___x_5135_; 
v___x_5135_ = 0;
return v___x_5135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6___boxed(lean_object* v_e_5136_){
_start:
{
uint8_t v_res_5137_; lean_object* v_r_5138_; 
v_res_5137_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6(v_e_5136_);
lean_dec_ref(v_e_5136_);
v_r_5138_ = lean_box(v_res_5137_);
return v_r_5138_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(lean_object* v_x_5139_){
_start:
{
if (lean_obj_tag(v_x_5139_) == 0)
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5148_; 
v_a_5141_ = lean_ctor_get(v_x_5139_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v_x_5139_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5143_ = v_x_5139_;
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v_x_5139_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5146_; 
if (v_isShared_5144_ == 0)
{
lean_ctor_set_tag(v___x_5143_, 1);
v___x_5146_ = v___x_5143_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5141_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
v_a_5149_ = lean_ctor_get(v_x_5139_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v_x_5139_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v_x_5139_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v_x_5139_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
lean_ctor_set_tag(v___x_5151_, 0);
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg___boxed(lean_object* v_x_5157_, lean_object* v___y_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_x_5157_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(lean_object* v_cls_5160_, uint8_t v_collapsed_5161_, lean_object* v_tag_5162_, lean_object* v_opts_5163_, uint8_t v_clsEnabled_5164_, lean_object* v_oldTraces_5165_, lean_object* v_msg_5166_, lean_object* v_resStartStop_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v_fst_5173_; lean_object* v_snd_5174_; lean_object* v___y_5176_; lean_object* v___y_5177_; lean_object* v_data_5178_; lean_object* v_fst_5189_; lean_object* v_snd_5190_; lean_object* v___x_5191_; uint8_t v___x_5192_; lean_object* v___y_5194_; lean_object* v_a_5195_; uint8_t v___y_5210_; double v___y_5242_; 
v_fst_5173_ = lean_ctor_get(v_resStartStop_5167_, 0);
lean_inc(v_fst_5173_);
v_snd_5174_ = lean_ctor_get(v_resStartStop_5167_, 1);
lean_inc(v_snd_5174_);
lean_dec_ref(v_resStartStop_5167_);
v_fst_5189_ = lean_ctor_get(v_snd_5174_, 0);
lean_inc(v_fst_5189_);
v_snd_5190_ = lean_ctor_get(v_snd_5174_, 1);
lean_inc(v_snd_5190_);
lean_dec(v_snd_5174_);
v___x_5191_ = l_Lean_trace_profiler;
v___x_5192_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5163_, v___x_5191_);
if (v___x_5192_ == 0)
{
v___y_5210_ = v___x_5192_;
goto v___jp_5209_;
}
else
{
lean_object* v___x_5247_; uint8_t v___x_5248_; 
v___x_5247_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5248_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5163_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5249_; lean_object* v___x_5250_; double v___x_5251_; double v___x_5252_; double v___x_5253_; 
v___x_5249_ = l_Lean_trace_profiler_threshold;
v___x_5250_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5163_, v___x_5249_);
v___x_5251_ = lean_float_of_nat(v___x_5250_);
v___x_5252_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5253_ = lean_float_div(v___x_5251_, v___x_5252_);
v___y_5242_ = v___x_5253_;
goto v___jp_5241_;
}
else
{
lean_object* v___x_5254_; lean_object* v___x_5255_; double v___x_5256_; 
v___x_5254_ = l_Lean_trace_profiler_threshold;
v___x_5255_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5163_, v___x_5254_);
v___x_5256_ = lean_float_of_nat(v___x_5255_);
v___y_5242_ = v___x_5256_;
goto v___jp_5241_;
}
}
v___jp_5175_:
{
lean_object* v___x_5179_; 
lean_inc(v___y_5177_);
v___x_5179_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(v_oldTraces_5165_, v_data_5178_, v___y_5177_, v___y_5176_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v___x_5180_; 
lean_dec_ref_known(v___x_5179_, 1);
v___x_5180_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_fst_5173_);
return v___x_5180_;
}
else
{
lean_object* v_a_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5188_; 
lean_dec(v_fst_5173_);
v_a_5181_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5183_ = v___x_5179_;
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_a_5181_);
lean_dec(v___x_5179_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5186_; 
if (v_isShared_5184_ == 0)
{
v___x_5186_ = v___x_5183_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
}
v___jp_5193_:
{
uint8_t v_result_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; double v___x_5199_; lean_object* v_data_5200_; 
v_result_5196_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__6(v_fst_5173_);
v___x_5197_ = lean_box(v_result_5196_);
v___x_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
v___x_5199_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5162_);
lean_inc_ref(v___x_5198_);
lean_inc(v_cls_5160_);
v_data_5200_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5200_, 0, v_cls_5160_);
lean_ctor_set(v_data_5200_, 1, v___x_5198_);
lean_ctor_set(v_data_5200_, 2, v_tag_5162_);
lean_ctor_set_float(v_data_5200_, sizeof(void*)*3, v___x_5199_);
lean_ctor_set_float(v_data_5200_, sizeof(void*)*3 + 8, v___x_5199_);
lean_ctor_set_uint8(v_data_5200_, sizeof(void*)*3 + 16, v_collapsed_5161_);
if (v___x_5192_ == 0)
{
lean_dec_ref_known(v___x_5198_, 1);
lean_dec(v_snd_5190_);
lean_dec(v_fst_5189_);
lean_dec_ref(v_tag_5162_);
lean_dec(v_cls_5160_);
v___y_5176_ = v_a_5195_;
v___y_5177_ = v___y_5194_;
v_data_5178_ = v_data_5200_;
goto v___jp_5175_;
}
else
{
lean_object* v_data_5201_; double v___x_5202_; double v___x_5203_; 
lean_dec_ref_known(v_data_5200_, 3);
v_data_5201_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5201_, 0, v_cls_5160_);
lean_ctor_set(v_data_5201_, 1, v___x_5198_);
lean_ctor_set(v_data_5201_, 2, v_tag_5162_);
v___x_5202_ = lean_unbox_float(v_fst_5189_);
lean_dec(v_fst_5189_);
lean_ctor_set_float(v_data_5201_, sizeof(void*)*3, v___x_5202_);
v___x_5203_ = lean_unbox_float(v_snd_5190_);
lean_dec(v_snd_5190_);
lean_ctor_set_float(v_data_5201_, sizeof(void*)*3 + 8, v___x_5203_);
lean_ctor_set_uint8(v_data_5201_, sizeof(void*)*3 + 16, v_collapsed_5161_);
v___y_5176_ = v_a_5195_;
v___y_5177_ = v___y_5194_;
v_data_5178_ = v_data_5201_;
goto v___jp_5175_;
}
}
v___jp_5204_:
{
lean_object* v_ref_5205_; lean_object* v___x_5206_; 
v_ref_5205_ = lean_ctor_get(v___y_5170_, 2);
lean_inc(v___y_5171_);
lean_inc_ref(v___y_5170_);
lean_inc(v___y_5169_);
lean_inc_ref(v___y_5168_);
lean_inc(v_fst_5173_);
v___x_5206_ = lean_apply_6(v_msg_5166_, v_fst_5173_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, lean_box(0));
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
lean_inc(v_a_5207_);
lean_dec_ref_known(v___x_5206_, 1);
v___y_5194_ = v_ref_5205_;
v_a_5195_ = v_a_5207_;
goto v___jp_5193_;
}
else
{
lean_object* v___x_5208_; 
lean_dec_ref_known(v___x_5206_, 1);
v___x_5208_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5194_ = v_ref_5205_;
v_a_5195_ = v___x_5208_;
goto v___jp_5193_;
}
}
v___jp_5209_:
{
if (v_clsEnabled_5164_ == 0)
{
if (v___y_5210_ == 0)
{
lean_object* v___x_5211_; lean_object* v_traceState_5212_; lean_object* v_env_5213_; lean_object* v_nextMacroScope_5214_; lean_object* v_ngen_5215_; lean_object* v_auxDeclNGen_5216_; lean_object* v_cache_5217_; lean_object* v_recordedDeps_5218_; lean_object* v_messages_5219_; lean_object* v_infoState_5220_; lean_object* v_snapshotTasks_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5240_; 
lean_dec(v_snd_5190_);
lean_dec(v_fst_5189_);
lean_dec_ref(v_msg_5166_);
lean_dec_ref(v_tag_5162_);
lean_dec(v_cls_5160_);
v___x_5211_ = lean_st_ref_take(v___y_5171_);
v_traceState_5212_ = lean_ctor_get(v___x_5211_, 4);
v_env_5213_ = lean_ctor_get(v___x_5211_, 0);
v_nextMacroScope_5214_ = lean_ctor_get(v___x_5211_, 1);
v_ngen_5215_ = lean_ctor_get(v___x_5211_, 2);
v_auxDeclNGen_5216_ = lean_ctor_get(v___x_5211_, 3);
v_cache_5217_ = lean_ctor_get(v___x_5211_, 5);
v_recordedDeps_5218_ = lean_ctor_get(v___x_5211_, 6);
v_messages_5219_ = lean_ctor_get(v___x_5211_, 7);
v_infoState_5220_ = lean_ctor_get(v___x_5211_, 8);
v_snapshotTasks_5221_ = lean_ctor_get(v___x_5211_, 9);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5223_ = v___x_5211_;
v_isShared_5224_ = v_isSharedCheck_5240_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_snapshotTasks_5221_);
lean_inc(v_infoState_5220_);
lean_inc(v_messages_5219_);
lean_inc(v_recordedDeps_5218_);
lean_inc(v_cache_5217_);
lean_inc(v_traceState_5212_);
lean_inc(v_auxDeclNGen_5216_);
lean_inc(v_ngen_5215_);
lean_inc(v_nextMacroScope_5214_);
lean_inc(v_env_5213_);
lean_dec(v___x_5211_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5240_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
uint64_t v_tid_5225_; lean_object* v_traces_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5239_; 
v_tid_5225_ = lean_ctor_get_uint64(v_traceState_5212_, sizeof(void*)*1);
v_traces_5226_ = lean_ctor_get(v_traceState_5212_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_traceState_5212_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5228_ = v_traceState_5212_;
v_isShared_5229_ = v_isSharedCheck_5239_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_traces_5226_);
lean_dec(v_traceState_5212_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5239_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5230_; lean_object* v___x_5232_; 
v___x_5230_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5165_, v_traces_5226_);
lean_dec_ref(v_traces_5226_);
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 0, v___x_5230_);
v___x_5232_ = v___x_5228_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5230_);
lean_ctor_set_uint64(v_reuseFailAlloc_5238_, sizeof(void*)*1, v_tid_5225_);
v___x_5232_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
lean_object* v___x_5234_; 
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 4, v___x_5232_);
v___x_5234_ = v___x_5223_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_env_5213_);
lean_ctor_set(v_reuseFailAlloc_5237_, 1, v_nextMacroScope_5214_);
lean_ctor_set(v_reuseFailAlloc_5237_, 2, v_ngen_5215_);
lean_ctor_set(v_reuseFailAlloc_5237_, 3, v_auxDeclNGen_5216_);
lean_ctor_set(v_reuseFailAlloc_5237_, 4, v___x_5232_);
lean_ctor_set(v_reuseFailAlloc_5237_, 5, v_cache_5217_);
lean_ctor_set(v_reuseFailAlloc_5237_, 6, v_recordedDeps_5218_);
lean_ctor_set(v_reuseFailAlloc_5237_, 7, v_messages_5219_);
lean_ctor_set(v_reuseFailAlloc_5237_, 8, v_infoState_5220_);
lean_ctor_set(v_reuseFailAlloc_5237_, 9, v_snapshotTasks_5221_);
v___x_5234_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5235_ = lean_st_ref_put(v___y_5171_, v___x_5234_);
v___x_5236_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_fst_5173_);
return v___x_5236_;
}
}
}
}
}
else
{
goto v___jp_5204_;
}
}
else
{
goto v___jp_5204_;
}
}
v___jp_5241_:
{
double v___x_5243_; double v___x_5244_; double v___x_5245_; uint8_t v___x_5246_; 
v___x_5243_ = lean_unbox_float(v_snd_5190_);
v___x_5244_ = lean_unbox_float(v_fst_5189_);
v___x_5245_ = lean_float_sub(v___x_5243_, v___x_5244_);
v___x_5246_ = lean_float_decLt(v___y_5242_, v___x_5245_);
v___y_5210_ = v___x_5246_;
goto v___jp_5209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3___boxed(lean_object* v_cls_5257_, lean_object* v_collapsed_5258_, lean_object* v_tag_5259_, lean_object* v_opts_5260_, lean_object* v_clsEnabled_5261_, lean_object* v_oldTraces_5262_, lean_object* v_msg_5263_, lean_object* v_resStartStop_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
uint8_t v_collapsed_boxed_5270_; uint8_t v_clsEnabled_boxed_5271_; lean_object* v_res_5272_; 
v_collapsed_boxed_5270_ = lean_unbox(v_collapsed_5258_);
v_clsEnabled_boxed_5271_ = lean_unbox(v_clsEnabled_5261_);
v_res_5272_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5257_, v_collapsed_boxed_5270_, v_tag_5259_, v_opts_5260_, v_clsEnabled_boxed_5271_, v_oldTraces_5262_, v_msg_5263_, v_resStartStop_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec_ref(v_opts_5260_);
return v_res_5272_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v_cls_5277_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5278_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5279_ = l_Lean_Name_append(v___x_5278_, v_cls_5277_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v___y_5287_; lean_object* v_toCold_5305_; lean_object* v_options_5306_; lean_object* v_inheritedTraceOptions_5307_; uint8_t v_hasTrace_5308_; lean_object* v_cls_5309_; uint8_t v___x_5310_; 
v_toCold_5305_ = lean_ctor_get(v_a_5283_, 0);
v_options_5306_ = lean_ctor_get(v_toCold_5305_, 2);
v_inheritedTraceOptions_5307_ = lean_ctor_get(v_toCold_5305_, 11);
v_hasTrace_5308_ = lean_ctor_get_uint8(v_options_5306_, sizeof(void*)*1);
v_cls_5309_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5310_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5280_);
if (v_hasTrace_5308_ == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5310_, v_e_5280_, v_cls_5309_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
v___y_5287_ = v___x_5311_;
goto v___jp_5286_;
}
else
{
lean_object* v___f_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; uint8_t v___x_5315_; lean_object* v___y_5317_; lean_object* v___y_5318_; lean_object* v_a_5319_; lean_object* v___y_5332_; lean_object* v___y_5333_; lean_object* v_a_5334_; 
v___f_5312_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5313_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5314_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5315_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5307_, v_options_5306_, v___x_5314_);
if (v___x_5315_ == 0)
{
lean_object* v___x_5384_; uint8_t v___x_5385_; 
v___x_5384_ = l_Lean_trace_profiler;
v___x_5385_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5306_, v___x_5384_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; 
v___x_5386_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5310_, v_e_5280_, v_cls_5309_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
v___y_5287_ = v___x_5386_;
goto v___jp_5286_;
}
else
{
goto v___jp_5343_;
}
}
else
{
goto v___jp_5343_;
}
v___jp_5316_:
{
lean_object* v___x_5320_; double v___x_5321_; double v___x_5322_; double v___x_5323_; double v___x_5324_; double v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5320_ = lean_io_mono_nanos_now();
v___x_5321_ = lean_float_of_nat(v___y_5318_);
v___x_5322_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5323_ = lean_float_div(v___x_5321_, v___x_5322_);
v___x_5324_ = lean_float_of_nat(v___x_5320_);
v___x_5325_ = lean_float_div(v___x_5324_, v___x_5322_);
v___x_5326_ = lean_box_float(v___x_5323_);
v___x_5327_ = lean_box_float(v___x_5325_);
v___x_5328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5326_);
lean_ctor_set(v___x_5328_, 1, v___x_5327_);
v___x_5329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5329_, 0, v_a_5319_);
lean_ctor_set(v___x_5329_, 1, v___x_5328_);
v___x_5330_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5309_, v_hasTrace_5308_, v___x_5313_, v_options_5306_, v___x_5315_, v___y_5317_, v___f_5312_, v___x_5329_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
v___y_5287_ = v___x_5330_;
goto v___jp_5286_;
}
v___jp_5331_:
{
lean_object* v___x_5335_; double v___x_5336_; double v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5335_ = lean_io_get_num_heartbeats();
v___x_5336_ = lean_float_of_nat(v___y_5333_);
v___x_5337_ = lean_float_of_nat(v___x_5335_);
v___x_5338_ = lean_box_float(v___x_5336_);
v___x_5339_ = lean_box_float(v___x_5337_);
v___x_5340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5338_);
lean_ctor_set(v___x_5340_, 1, v___x_5339_);
v___x_5341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5341_, 0, v_a_5334_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5309_, v_hasTrace_5308_, v___x_5313_, v_options_5306_, v___x_5315_, v___y_5332_, v___f_5312_, v___x_5341_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
v___y_5287_ = v___x_5342_;
goto v___jp_5286_;
}
v___jp_5343_:
{
lean_object* v___x_5344_; lean_object* v_a_5345_; lean_object* v___x_5346_; uint8_t v___x_5347_; 
v___x_5344_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v_a_5284_);
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
lean_inc(v_a_5345_);
lean_dec_ref(v___x_5344_);
v___x_5346_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5347_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5306_, v___x_5346_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5348_ = lean_io_mono_nanos_now();
v___x_5349_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5310_, v_e_5280_, v_cls_5309_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
if (lean_obj_tag(v___x_5349_) == 0)
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
v_a_5350_ = lean_ctor_get(v___x_5349_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5349_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5349_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
lean_ctor_set_tag(v___x_5352_, 1);
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
v___y_5317_ = v_a_5345_;
v___y_5318_ = v___x_5348_;
v_a_5319_ = v___x_5355_;
goto v___jp_5316_;
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
v_a_5358_ = lean_ctor_get(v___x_5349_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5349_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5349_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
lean_ctor_set_tag(v___x_5360_, 0);
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
v___y_5317_ = v_a_5345_;
v___y_5318_ = v___x_5348_;
v_a_5319_ = v___x_5363_;
goto v___jp_5316_;
}
}
}
}
else
{
lean_object* v___x_5366_; lean_object* v___x_5367_; 
v___x_5366_ = lean_io_get_num_heartbeats();
v___x_5367_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5310_, v_e_5280_, v_cls_5309_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
if (lean_obj_tag(v___x_5367_) == 0)
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
v_a_5368_ = lean_ctor_get(v___x_5367_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___x_5367_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5367_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
lean_ctor_set_tag(v___x_5370_, 1);
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
v___y_5332_ = v_a_5345_;
v___y_5333_ = v___x_5366_;
v_a_5334_ = v___x_5373_;
goto v___jp_5331_;
}
}
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
v_a_5376_ = lean_ctor_get(v___x_5367_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5367_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5367_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
lean_ctor_set_tag(v___x_5378_, 0);
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
v___y_5332_ = v_a_5345_;
v___y_5333_ = v___x_5366_;
v_a_5334_ = v___x_5381_;
goto v___jp_5331_;
}
}
}
}
}
}
v___jp_5286_:
{
if (lean_obj_tag(v___y_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5296_; 
v_a_5288_ = lean_ctor_get(v___y_5287_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___y_5287_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5290_ = v___y_5287_;
v_isShared_5291_ = v_isSharedCheck_5296_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___y_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5296_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v_fst_5292_; lean_object* v___x_5294_; 
v_fst_5292_ = lean_ctor_get(v_a_5288_, 0);
lean_inc(v_fst_5292_);
lean_dec(v_a_5288_);
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v_fst_5292_);
v___x_5294_ = v___x_5290_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_fst_5292_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
else
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5304_; 
v_a_5297_ = lean_ctor_get(v___y_5287_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___y_5287_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5299_ = v___y_5287_;
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___y_5287_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5302_; 
if (v_isShared_5300_ == 0)
{
v___x_5302_ = v___x_5299_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_);
lean_dec(v_a_5391_);
lean_dec_ref(v_a_5390_);
lean_dec(v_a_5389_);
lean_dec_ref(v_a_5388_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1_spec__1(lean_object* v_00_u03b2_5394_){
_start:
{
lean_object* v___x_5395_; 
v___x_5395_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(){
_start:
{
lean_object* v___x_5397_; 
v___x_5397_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___dummy_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg();
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v_00_u03b2_5400_){
_start:
{
lean_object* v___x_5401_; 
v___x_5401_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5(lean_object* v_00_u03b1_5402_, lean_object* v_x_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v___x_5409_; 
v___x_5409_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_x_5403_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___boxed(lean_object* v_00_u03b1_5410_, lean_object* v_x_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5(v_00_u03b1_5410_, v_x_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec(v___y_5413_);
lean_dec_ref(v___y_5412_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5418_, lean_object* v___y_5419_){
_start:
{
uint8_t v___x_5421_; 
v___x_5421_ = l_Lean_Expr_hasMVar(v_e_5418_);
if (v___x_5421_ == 0)
{
lean_object* v___x_5422_; 
v___x_5422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5422_, 0, v_e_5418_);
return v___x_5422_;
}
else
{
lean_object* v___x_5423_; lean_object* v_mctx_5424_; lean_object* v___x_5425_; lean_object* v_fst_5426_; lean_object* v_snd_5427_; lean_object* v___x_5428_; lean_object* v_cache_5429_; lean_object* v_zetaDeltaFVarIds_5430_; lean_object* v_postponed_5431_; lean_object* v_diag_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5441_; 
v___x_5423_ = lean_st_ref_get(v___y_5419_);
v_mctx_5424_ = lean_ctor_get(v___x_5423_, 0);
lean_inc_ref(v_mctx_5424_);
lean_dec(v___x_5423_);
v___x_5425_ = l_Lean_instantiateMVarsCore(v_mctx_5424_, v_e_5418_);
v_fst_5426_ = lean_ctor_get(v___x_5425_, 0);
lean_inc(v_fst_5426_);
v_snd_5427_ = lean_ctor_get(v___x_5425_, 1);
lean_inc(v_snd_5427_);
lean_dec_ref(v___x_5425_);
v___x_5428_ = lean_st_ref_take(v___y_5419_);
v_cache_5429_ = lean_ctor_get(v___x_5428_, 1);
v_zetaDeltaFVarIds_5430_ = lean_ctor_get(v___x_5428_, 2);
v_postponed_5431_ = lean_ctor_get(v___x_5428_, 3);
v_diag_5432_ = lean_ctor_get(v___x_5428_, 4);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5441_ == 0)
{
lean_object* v_unused_5442_; 
v_unused_5442_ = lean_ctor_get(v___x_5428_, 0);
lean_dec(v_unused_5442_);
v___x_5434_ = v___x_5428_;
v_isShared_5435_ = v_isSharedCheck_5441_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_diag_5432_);
lean_inc(v_postponed_5431_);
lean_inc(v_zetaDeltaFVarIds_5430_);
lean_inc(v_cache_5429_);
lean_dec(v___x_5428_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5441_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 0, v_snd_5427_);
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_snd_5427_);
lean_ctor_set(v_reuseFailAlloc_5440_, 1, v_cache_5429_);
lean_ctor_set(v_reuseFailAlloc_5440_, 2, v_zetaDeltaFVarIds_5430_);
lean_ctor_set(v_reuseFailAlloc_5440_, 3, v_postponed_5431_);
lean_ctor_set(v_reuseFailAlloc_5440_, 4, v_diag_5432_);
v___x_5437_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; 
v___x_5438_ = lean_st_ref_put(v___y_5419_, v___x_5437_);
v___x_5439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5439_, 0, v_fst_5426_);
return v___x_5439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5443_, v___y_5444_);
lean_dec(v___y_5444_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_){
_start:
{
lean_object* v___x_5453_; 
v___x_5453_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5447_, v___y_5449_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v_res_5460_; 
v_res_5460_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5461_, lean_object* v_opts_5462_, lean_object* v_act_5463_, lean_object* v_decl_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; 
lean_inc(v___y_5468_);
lean_inc_ref(v___y_5467_);
lean_inc(v___y_5466_);
lean_inc_ref(v___y_5465_);
v___x_5470_ = lean_apply_4(v_act_5463_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_);
v___x_5471_ = l_Lean_profileitIOUnsafe___redArg(v_category_5461_, v_opts_5462_, v___x_5470_, v_decl_5464_);
return v___x_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5472_, lean_object* v_opts_5473_, lean_object* v_act_5474_, lean_object* v_decl_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_){
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5472_, v_opts_5473_, v_act_5474_, v_decl_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec_ref(v_opts_5473_);
lean_dec_ref(v_category_5472_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5482_, lean_object* v_category_5483_, lean_object* v_opts_5484_, lean_object* v_act_5485_, lean_object* v_decl_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_){
_start:
{
lean_object* v___x_5492_; 
v___x_5492_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5483_, v_opts_5484_, v_act_5485_, v_decl_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5493_, lean_object* v_category_5494_, lean_object* v_opts_5495_, lean_object* v_act_5496_, lean_object* v_decl_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5493_, v_category_5494_, v_opts_5495_, v_act_5496_, v_decl_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
lean_dec(v___y_5499_);
lean_dec_ref(v___y_5498_);
lean_dec_ref(v_opts_5495_);
lean_dec_ref(v_category_5494_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5504_, uint8_t v_isExporting_5505_, lean_object* v___x_5506_, lean_object* v___y_5507_, lean_object* v___x_5508_, lean_object* v_a_x3f_5509_){
_start:
{
lean_object* v___x_5511_; lean_object* v_env_5512_; lean_object* v_nextMacroScope_5513_; lean_object* v_ngen_5514_; lean_object* v_auxDeclNGen_5515_; lean_object* v_traceState_5516_; lean_object* v_recordedDeps_5517_; lean_object* v_messages_5518_; lean_object* v_infoState_5519_; lean_object* v_snapshotTasks_5520_; lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5545_; 
v___x_5511_ = lean_st_ref_take(v___y_5504_);
v_env_5512_ = lean_ctor_get(v___x_5511_, 0);
v_nextMacroScope_5513_ = lean_ctor_get(v___x_5511_, 1);
v_ngen_5514_ = lean_ctor_get(v___x_5511_, 2);
v_auxDeclNGen_5515_ = lean_ctor_get(v___x_5511_, 3);
v_traceState_5516_ = lean_ctor_get(v___x_5511_, 4);
v_recordedDeps_5517_ = lean_ctor_get(v___x_5511_, 6);
v_messages_5518_ = lean_ctor_get(v___x_5511_, 7);
v_infoState_5519_ = lean_ctor_get(v___x_5511_, 8);
v_snapshotTasks_5520_ = lean_ctor_get(v___x_5511_, 9);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5511_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; 
v_unused_5546_ = lean_ctor_get(v___x_5511_, 5);
lean_dec(v_unused_5546_);
v___x_5522_ = v___x_5511_;
v_isShared_5523_ = v_isSharedCheck_5545_;
goto v_resetjp_5521_;
}
else
{
lean_inc(v_snapshotTasks_5520_);
lean_inc(v_infoState_5519_);
lean_inc(v_messages_5518_);
lean_inc(v_recordedDeps_5517_);
lean_inc(v_traceState_5516_);
lean_inc(v_auxDeclNGen_5515_);
lean_inc(v_ngen_5514_);
lean_inc(v_nextMacroScope_5513_);
lean_inc(v_env_5512_);
lean_dec(v___x_5511_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5545_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
lean_object* v___x_5524_; lean_object* v___x_5526_; 
v___x_5524_ = l_Lean_Environment_setExporting(v_env_5512_, v_isExporting_5505_);
if (v_isShared_5523_ == 0)
{
lean_ctor_set(v___x_5522_, 5, v___x_5506_);
lean_ctor_set(v___x_5522_, 0, v___x_5524_);
v___x_5526_ = v___x_5522_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5524_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v_nextMacroScope_5513_);
lean_ctor_set(v_reuseFailAlloc_5544_, 2, v_ngen_5514_);
lean_ctor_set(v_reuseFailAlloc_5544_, 3, v_auxDeclNGen_5515_);
lean_ctor_set(v_reuseFailAlloc_5544_, 4, v_traceState_5516_);
lean_ctor_set(v_reuseFailAlloc_5544_, 5, v___x_5506_);
lean_ctor_set(v_reuseFailAlloc_5544_, 6, v_recordedDeps_5517_);
lean_ctor_set(v_reuseFailAlloc_5544_, 7, v_messages_5518_);
lean_ctor_set(v_reuseFailAlloc_5544_, 8, v_infoState_5519_);
lean_ctor_set(v_reuseFailAlloc_5544_, 9, v_snapshotTasks_5520_);
v___x_5526_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v_mctx_5529_; lean_object* v_zetaDeltaFVarIds_5530_; lean_object* v_postponed_5531_; lean_object* v_diag_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5542_; 
v___x_5527_ = lean_st_ref_put(v___y_5504_, v___x_5526_);
v___x_5528_ = lean_st_ref_take(v___y_5507_);
v_mctx_5529_ = lean_ctor_get(v___x_5528_, 0);
v_zetaDeltaFVarIds_5530_ = lean_ctor_get(v___x_5528_, 2);
v_postponed_5531_ = lean_ctor_get(v___x_5528_, 3);
v_diag_5532_ = lean_ctor_get(v___x_5528_, 4);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5528_);
if (v_isSharedCheck_5542_ == 0)
{
lean_object* v_unused_5543_; 
v_unused_5543_ = lean_ctor_get(v___x_5528_, 1);
lean_dec(v_unused_5543_);
v___x_5534_ = v___x_5528_;
v_isShared_5535_ = v_isSharedCheck_5542_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_diag_5532_);
lean_inc(v_postponed_5531_);
lean_inc(v_zetaDeltaFVarIds_5530_);
lean_inc(v_mctx_5529_);
lean_dec(v___x_5528_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5542_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5536_; lean_object* v___x_5538_; 
v___x_5536_ = lean_box(0);
if (v_isShared_5535_ == 0)
{
lean_ctor_set(v___x_5534_, 1, v___x_5508_);
v___x_5538_ = v___x_5534_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_mctx_5529_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v___x_5508_);
lean_ctor_set(v_reuseFailAlloc_5541_, 2, v_zetaDeltaFVarIds_5530_);
lean_ctor_set(v_reuseFailAlloc_5541_, 3, v_postponed_5531_);
lean_ctor_set(v_reuseFailAlloc_5541_, 4, v_diag_5532_);
v___x_5538_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
lean_object* v___x_5539_; lean_object* v___x_5540_; 
v___x_5539_ = lean_st_ref_put(v___y_5507_, v___x_5538_);
v___x_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5540_, 0, v___x_5536_);
return v___x_5540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5547_, lean_object* v_isExporting_5548_, lean_object* v___x_5549_, lean_object* v___y_5550_, lean_object* v___x_5551_, lean_object* v_a_x3f_5552_, lean_object* v___y_5553_){
_start:
{
uint8_t v_isExporting_boxed_5554_; lean_object* v_res_5555_; 
v_isExporting_boxed_5554_ = lean_unbox(v_isExporting_5548_);
v_res_5555_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5547_, v_isExporting_boxed_5554_, v___x_5549_, v___y_5550_, v___x_5551_, v_a_x3f_5552_);
lean_dec(v_a_x3f_5552_);
lean_dec(v___y_5550_);
lean_dec(v___y_5547_);
return v_res_5555_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; 
v___x_5556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_5557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5556_);
return v___x_5557_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5558_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5558_);
lean_ctor_set(v___x_5559_, 1, v___x_5558_);
return v___x_5559_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5560_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5561_, 0, v___x_5560_);
lean_ctor_set(v___x_5561_, 1, v___x_5560_);
return v___x_5561_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
v___x_5562_ = lean_unsigned_to_nat(0u);
v___x_5563_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5563_);
lean_ctor_set(v___x_5564_, 1, v___x_5563_);
lean_ctor_set(v___x_5564_, 2, v___x_5562_);
return v___x_5564_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
v___x_5565_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
v___x_5566_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
v___x_5567_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5568_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
v___x_5569_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5568_);
lean_ctor_set(v___x_5569_, 1, v___x_5567_);
lean_ctor_set(v___x_5569_, 2, v___x_5566_);
lean_ctor_set(v___x_5569_, 3, v___x_5567_);
lean_ctor_set(v___x_5569_, 4, v___x_5567_);
lean_ctor_set(v___x_5569_, 5, v___x_5567_);
lean_ctor_set(v___x_5569_, 6, v___x_5565_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5570_, uint8_t v_isExporting_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
lean_object* v___x_5577_; lean_object* v_env_5578_; lean_object* v___x_5579_; uint8_t v_isModule_5580_; 
v___x_5577_ = lean_st_ref_get(v___y_5575_);
v_env_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc_ref(v_env_5578_);
lean_dec(v___x_5577_);
v___x_5579_ = l_Lean_Environment_header(v_env_5578_);
v_isModule_5580_ = lean_ctor_get_uint8(v___x_5579_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5579_);
if (v_isModule_5580_ == 0)
{
lean_object* v___x_5581_; 
lean_dec_ref(v_env_5578_);
lean_inc(v___y_5575_);
lean_inc_ref(v___y_5574_);
lean_inc(v___y_5573_);
lean_inc_ref(v___y_5572_);
v___x_5581_ = lean_apply_5(v_x_5570_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, lean_box(0));
return v___x_5581_;
}
else
{
uint8_t v_isExporting_5582_; 
v_isExporting_5582_ = lean_ctor_get_uint8(v_env_5578_, sizeof(void*)*13);
lean_dec_ref(v_env_5578_);
if (v_isExporting_5571_ == 0)
{
if (v_isExporting_5582_ == 0)
{
lean_object* v___x_5649_; 
lean_inc(v___y_5575_);
lean_inc_ref(v___y_5574_);
lean_inc(v___y_5573_);
lean_inc_ref(v___y_5572_);
v___x_5649_ = lean_apply_5(v_x_5570_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, lean_box(0));
return v___x_5649_;
}
else
{
goto v___jp_5583_;
}
}
else
{
if (v_isExporting_5582_ == 0)
{
goto v___jp_5583_;
}
else
{
lean_object* v___x_5650_; 
lean_inc(v___y_5575_);
lean_inc_ref(v___y_5574_);
lean_inc(v___y_5573_);
lean_inc_ref(v___y_5572_);
v___x_5650_ = lean_apply_5(v_x_5570_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, lean_box(0));
return v___x_5650_;
}
}
v___jp_5583_:
{
lean_object* v___x_5584_; lean_object* v_env_5585_; lean_object* v_nextMacroScope_5586_; lean_object* v_ngen_5587_; lean_object* v_auxDeclNGen_5588_; lean_object* v_traceState_5589_; lean_object* v_recordedDeps_5590_; lean_object* v_messages_5591_; lean_object* v_infoState_5592_; lean_object* v_snapshotTasks_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5647_; 
v___x_5584_ = lean_st_ref_take(v___y_5575_);
v_env_5585_ = lean_ctor_get(v___x_5584_, 0);
v_nextMacroScope_5586_ = lean_ctor_get(v___x_5584_, 1);
v_ngen_5587_ = lean_ctor_get(v___x_5584_, 2);
v_auxDeclNGen_5588_ = lean_ctor_get(v___x_5584_, 3);
v_traceState_5589_ = lean_ctor_get(v___x_5584_, 4);
v_recordedDeps_5590_ = lean_ctor_get(v___x_5584_, 6);
v_messages_5591_ = lean_ctor_get(v___x_5584_, 7);
v_infoState_5592_ = lean_ctor_get(v___x_5584_, 8);
v_snapshotTasks_5593_ = lean_ctor_get(v___x_5584_, 9);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; 
v_unused_5648_ = lean_ctor_get(v___x_5584_, 5);
lean_dec(v_unused_5648_);
v___x_5595_ = v___x_5584_;
v_isShared_5596_ = v_isSharedCheck_5647_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_snapshotTasks_5593_);
lean_inc(v_infoState_5592_);
lean_inc(v_messages_5591_);
lean_inc(v_recordedDeps_5590_);
lean_inc(v_traceState_5589_);
lean_inc(v_auxDeclNGen_5588_);
lean_inc(v_ngen_5587_);
lean_inc(v_nextMacroScope_5586_);
lean_inc(v_env_5585_);
lean_dec(v___x_5584_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5647_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5600_; 
v___x_5597_ = l_Lean_Environment_setExporting(v_env_5585_, v_isExporting_5571_);
v___x_5598_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 5, v___x_5598_);
lean_ctor_set(v___x_5595_, 0, v___x_5597_);
v___x_5600_ = v___x_5595_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5597_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_nextMacroScope_5586_);
lean_ctor_set(v_reuseFailAlloc_5646_, 2, v_ngen_5587_);
lean_ctor_set(v_reuseFailAlloc_5646_, 3, v_auxDeclNGen_5588_);
lean_ctor_set(v_reuseFailAlloc_5646_, 4, v_traceState_5589_);
lean_ctor_set(v_reuseFailAlloc_5646_, 5, v___x_5598_);
lean_ctor_set(v_reuseFailAlloc_5646_, 6, v_recordedDeps_5590_);
lean_ctor_set(v_reuseFailAlloc_5646_, 7, v_messages_5591_);
lean_ctor_set(v_reuseFailAlloc_5646_, 8, v_infoState_5592_);
lean_ctor_set(v_reuseFailAlloc_5646_, 9, v_snapshotTasks_5593_);
v___x_5600_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v_mctx_5603_; lean_object* v_zetaDeltaFVarIds_5604_; lean_object* v_postponed_5605_; lean_object* v_diag_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5644_; 
v___x_5601_ = lean_st_ref_put(v___y_5575_, v___x_5600_);
v___x_5602_ = lean_st_ref_take(v___y_5573_);
v_mctx_5603_ = lean_ctor_get(v___x_5602_, 0);
v_zetaDeltaFVarIds_5604_ = lean_ctor_get(v___x_5602_, 2);
v_postponed_5605_ = lean_ctor_get(v___x_5602_, 3);
v_diag_5606_ = lean_ctor_get(v___x_5602_, 4);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5602_);
if (v_isSharedCheck_5644_ == 0)
{
lean_object* v_unused_5645_; 
v_unused_5645_ = lean_ctor_get(v___x_5602_, 1);
lean_dec(v_unused_5645_);
v___x_5608_ = v___x_5602_;
v_isShared_5609_ = v_isSharedCheck_5644_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_diag_5606_);
lean_inc(v_postponed_5605_);
lean_inc(v_zetaDeltaFVarIds_5604_);
lean_inc(v_mctx_5603_);
lean_dec(v___x_5602_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5644_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5610_; lean_object* v___x_5612_; 
v___x_5610_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__4, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__4_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__4);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 1, v___x_5610_);
v___x_5612_ = v___x_5608_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_mctx_5603_);
lean_ctor_set(v_reuseFailAlloc_5643_, 1, v___x_5610_);
lean_ctor_set(v_reuseFailAlloc_5643_, 2, v_zetaDeltaFVarIds_5604_);
lean_ctor_set(v_reuseFailAlloc_5643_, 3, v_postponed_5605_);
lean_ctor_set(v_reuseFailAlloc_5643_, 4, v_diag_5606_);
v___x_5612_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
lean_object* v___x_5613_; lean_object* v_r_5614_; 
v___x_5613_ = lean_st_ref_put(v___y_5573_, v___x_5612_);
lean_inc(v___y_5575_);
lean_inc_ref(v___y_5574_);
lean_inc(v___y_5573_);
lean_inc_ref(v___y_5572_);
v_r_5614_ = lean_apply_5(v_x_5570_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, lean_box(0));
if (lean_obj_tag(v_r_5614_) == 0)
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5631_; 
v_a_5615_ = lean_ctor_get(v_r_5614_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v_r_5614_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5617_ = v_r_5614_;
v_isShared_5618_ = v_isSharedCheck_5631_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v_r_5614_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5631_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
lean_inc(v_a_5615_);
if (v_isShared_5618_ == 0)
{
lean_ctor_set_tag(v___x_5617_, 1);
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
lean_object* v___x_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
v___x_5621_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5575_, v_isExporting_5582_, v___x_5598_, v___y_5573_, v___x_5610_, v___x_5620_);
lean_dec_ref(v___x_5620_);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5621_);
if (v_isSharedCheck_5628_ == 0)
{
lean_object* v_unused_5629_; 
v_unused_5629_ = lean_ctor_get(v___x_5621_, 0);
lean_dec(v_unused_5629_);
v___x_5623_ = v___x_5621_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_dec(v___x_5621_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
lean_ctor_set(v___x_5623_, 0, v_a_5615_);
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5615_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5641_; 
v_a_5632_ = lean_ctor_get(v_r_5614_, 0);
lean_inc(v_a_5632_);
lean_dec_ref_known(v_r_5614_, 1);
v___x_5633_ = lean_box(0);
v___x_5634_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5575_, v_isExporting_5582_, v___x_5598_, v___y_5573_, v___x_5610_, v___x_5633_);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5634_);
if (v_isSharedCheck_5641_ == 0)
{
lean_object* v_unused_5642_; 
v_unused_5642_ = lean_ctor_get(v___x_5634_, 0);
lean_dec(v_unused_5642_);
v___x_5636_ = v___x_5634_;
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
else
{
lean_dec(v___x_5634_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5639_; 
if (v_isShared_5637_ == 0)
{
lean_ctor_set_tag(v___x_5636_, 1);
lean_ctor_set(v___x_5636_, 0, v_a_5632_);
v___x_5639_ = v___x_5636_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5632_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5651_, lean_object* v_isExporting_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
uint8_t v_isExporting_boxed_5658_; lean_object* v_res_5659_; 
v_isExporting_boxed_5658_ = lean_unbox(v_isExporting_5652_);
v_res_5659_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5651_, v_isExporting_boxed_5658_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec_ref(v___y_5653_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5660_, uint8_t v_when_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_){
_start:
{
if (v_when_5661_ == 0)
{
lean_object* v___x_5667_; 
lean_inc(v___y_5665_);
lean_inc_ref(v___y_5664_);
lean_inc(v___y_5663_);
lean_inc_ref(v___y_5662_);
v___x_5667_ = lean_apply_5(v_x_5660_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_, lean_box(0));
return v___x_5667_;
}
else
{
uint8_t v___x_5668_; lean_object* v___x_5669_; 
v___x_5668_ = 0;
v___x_5669_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5660_, v___x_5668_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_);
return v___x_5669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5670_, lean_object* v_when_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_){
_start:
{
uint8_t v_when_boxed_5677_; lean_object* v_res_5678_; 
v_when_boxed_5677_ = lean_unbox(v_when_5671_);
v_res_5678_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5670_, v_when_boxed_5677_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5673_);
lean_dec_ref(v___y_5672_);
return v_res_5678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_){
_start:
{
lean_object* v___x_5685_; lean_object* v_a_5686_; lean_object* v___x_5687_; uint8_t v___x_5688_; lean_object* v___x_5689_; 
v___x_5685_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5679_, v___y_5681_);
v_a_5686_ = lean_ctor_get(v___x_5685_, 0);
lean_inc(v_a_5686_);
lean_dec_ref(v___x_5685_);
v___x_5687_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5687_, 0, v_a_5686_);
v___x_5688_ = 1;
v___x_5689_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5687_, v___x_5688_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_);
return v___x_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l_Lean_Meta_letToHave___lam__0(v_e_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
lean_dec(v___y_5694_);
lean_dec_ref(v___y_5693_);
lean_dec(v___y_5692_);
lean_dec_ref(v___y_5691_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_){
_start:
{
lean_object* v___f_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; 
v___f_5704_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5704_, 0, v_e_5698_);
v___x_5705_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5701_);
v___x_5706_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5707_ = lean_box(0);
v___x_5708_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5706_, v___x_5705_, v___f_5704_, v___x_5707_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
lean_dec_ref(v___x_5705_);
return v___x_5708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_){
_start:
{
lean_object* v_res_5715_; 
v_res_5715_ = l_Lean_Meta_letToHave(v_e_5709_, v_a_5710_, v_a_5711_, v_a_5712_, v_a_5713_);
lean_dec(v_a_5713_);
lean_dec_ref(v_a_5712_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
return v_res_5715_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5716_, lean_object* v_x_5717_, uint8_t v_when_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_){
_start:
{
lean_object* v___x_5724_; 
v___x_5724_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5717_, v_when_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_);
return v___x_5724_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5725_, lean_object* v_x_5726_, lean_object* v_when_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_){
_start:
{
uint8_t v_when_boxed_5733_; lean_object* v_res_5734_; 
v_when_boxed_5733_ = lean_unbox(v_when_5727_);
v_res_5734_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5725_, v_x_5726_, v_when_boxed_5733_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5735_, lean_object* v_x_5736_, uint8_t v_isExporting_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_){
_start:
{
lean_object* v___x_5743_; 
v___x_5743_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5736_, v_isExporting_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
return v___x_5743_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5744_, lean_object* v_x_5745_, lean_object* v_isExporting_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_){
_start:
{
uint8_t v_isExporting_boxed_5752_; lean_object* v_res_5753_; 
v_isExporting_boxed_5752_ = lean_unbox(v_isExporting_5746_);
v_res_5753_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5744_, v_x_5745_, v_isExporting_boxed_5752_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_);
lean_dec(v___y_5750_);
lean_dec_ref(v___y_5749_);
lean_dec(v___y_5748_);
lean_dec_ref(v___y_5747_);
return v_res_5753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5810_; uint8_t v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; 
v___x_5810_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5811_ = 0;
v___x_5812_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5813_ = l_Lean_registerTraceClass(v___x_5810_, v___x_5811_, v___x_5812_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v___x_5814_; lean_object* v___x_5815_; 
lean_dec_ref_known(v___x_5813_, 1);
v___x_5814_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5815_ = l_Lean_registerTraceClass(v___x_5814_, v___x_5811_, v___x_5812_);
return v___x_5815_;
}
else
{
return v___x_5813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5817_;
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
