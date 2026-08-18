// Lean compiler output
// Module: Lean.Elab.Deriving.Inhabited
// Imports: public import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_runST___redArg(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_inlineExprTrailing(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inhabited"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(101, 188, 179, 164, 47, 207, 0, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "adding local instance "};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__15_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__18_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__19_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__20_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__18_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__20_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__0_value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__6_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__12_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__14_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__16_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__18_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__21_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__24_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__28_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__29_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "synthesizing Inhabited instance for"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "value:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "using structure instance elaborator"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "using constructor `"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Elab.Deriving.Inhabited"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "_private.Lean.Elab.Deriving.Inhabited.0.Lean.Elab.Deriving.mkInhabitedInstanceUsing.mkDefaultValue"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "assertion violation: insts'.size == usedInstIdxs.size\n      "};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "inhabited instance using"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "(assuming parameters "};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " are inhabited)"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "default value contains metavariables"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cannot unify"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "\nand type of constructor"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "structInstDefault"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value),LEAN_SCALAR_PTR_LITERAL(45, 130, 215, 216, 160, 223, 59, 11)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "struct_inst_default%"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "defined "};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "failed to generate `Inhabited` instance for `"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__1_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__1_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__1_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__2_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__1_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__2_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__2_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__3_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__2_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__3_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__3_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__4_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__3_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__4_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__4_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__5_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__4_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__5_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__5_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__6_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__5_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 164, 70, 31, 206, 252, 238, 147)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__6_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__6_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__7_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__6_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(140, 194, 148, 125, 144, 72, 62, 221)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__7_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__7_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__8_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__7_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 4, 236, 13, 233, 47, 93, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__8_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__8_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__9_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__8_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 114, 45, 173, 48, 103, 133, 91)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__9_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__9_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__10_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__9_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 110, 74, 211, 44, 224, 59, 89)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__10_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__10_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__11_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__11_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__11_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__12_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__10_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__11_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 17, 103, 136, 133, 202, 5, 190)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__12_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__12_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__13_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__13_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__13_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__14_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__12_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__13_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 134, 54, 140, 94, 30, 17, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__14_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__14_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__15_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__14_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(192, 173, 29, 242, 158, 136, 98, 37)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__15_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__15_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__16_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__15_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 34, 34, 83, 128, 253, 59, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__16_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__16_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__17_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__16_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 201, 103, 246, 90, 145, 218, 30)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__17_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__17_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__18_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__17_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 85, 122, 167, 214, 70, 252, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__18_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__18_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__19_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__18_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1810264634) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(173, 158, 179, 196, 115, 230, 94, 231)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__19_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__19_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__20_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__20_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__20_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__21_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__19_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__20_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 194, 80, 207, 143, 169, 212, 250)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__21_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__21_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__22_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__22_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__22_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__23_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__21_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__22_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 130, 173, 197, 75, 117, 10, 48)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__23_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__23_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__23_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(59, 196, 71, 140, 178, 60, 124, 70)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v_b_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_10_ = lean_apply_8(v_k_1_, v_b_4_, v___y_2_, v___y_3_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v_b_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0(v_k_11_, v___y_12_, v___y_13_, v_b_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(lean_object* v_name_21_, uint8_t v_bi_22_, lean_object* v_type_23_, lean_object* v_k_24_, uint8_t v_kind_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___f_33_; lean_object* v___x_34_; 
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
v___f_33_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_33_, 0, v_k_24_);
lean_closure_set(v___f_33_, 1, v___y_26_);
lean_closure_set(v___f_33_, 2, v___y_27_);
v___x_34_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_21_, v_bi_22_, v_type_23_, v___f_33_, v_kind_25_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_34_) == 0)
{
return v___x_34_;
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___boxed(lean_object* v_name_43_, lean_object* v_bi_44_, lean_object* v_type_45_, lean_object* v_k_46_, lean_object* v_kind_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_bi_boxed_55_; uint8_t v_kind_boxed_56_; lean_object* v_res_57_; 
v_bi_boxed_55_ = lean_unbox(v_bi_44_);
v_kind_boxed_56_ = lean_unbox(v_kind_47_);
v_res_57_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_name_43_, v_bi_boxed_55_, v_type_45_, v_k_46_, v_kind_boxed_56_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1(lean_object* v_00_u03b1_58_, lean_object* v_name_59_, uint8_t v_bi_60_, lean_object* v_type_61_, lean_object* v_k_62_, uint8_t v_kind_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_name_59_, v_bi_60_, v_type_61_, v_k_62_, v_kind_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___boxed(lean_object* v_00_u03b1_72_, lean_object* v_name_73_, lean_object* v_bi_74_, lean_object* v_type_75_, lean_object* v_k_76_, lean_object* v_kind_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v_bi_boxed_85_; uint8_t v_kind_boxed_86_; lean_object* v_res_87_; 
v_bi_boxed_85_ = lean_unbox(v_bi_74_);
v_kind_boxed_86_ = lean_unbox(v_kind_77_);
v_res_87_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1(v_00_u03b1_72_, v_name_73_, v_bi_boxed_85_, v_type_75_, v_k_76_, v_kind_boxed_86_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(lean_object* v_msgData_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_env_95_; lean_object* v___x_96_; lean_object* v_mctx_97_; lean_object* v_lctx_98_; lean_object* v_options_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_94_ = lean_st_ref_get(v___y_92_);
v_env_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_env_95_);
lean_dec(v___x_94_);
v___x_96_ = lean_st_ref_get(v___y_90_);
v_mctx_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_mctx_97_);
lean_dec(v___x_96_);
v_lctx_98_ = lean_ctor_get(v___y_89_, 2);
v_options_99_ = lean_ctor_get(v___y_91_, 2);
lean_inc_ref(v_options_99_);
lean_inc_ref(v_lctx_98_);
v___x_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_100_, 0, v_env_95_);
lean_ctor_set(v___x_100_, 1, v_mctx_97_);
lean_ctor_set(v___x_100_, 2, v_lctx_98_);
lean_ctor_set(v___x_100_, 3, v_options_99_);
v___x_101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_msgData_88_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0___boxed(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msgData_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_110_; double v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_float_of_nat(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(lean_object* v_cls_115_, lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_ref_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_168_; 
v_ref_122_ = lean_ctor_get(v___y_119_, 5);
v___x_123_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_168_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_168_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_168_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v_traceState_129_; lean_object* v_env_130_; lean_object* v_nextMacroScope_131_; lean_object* v_ngen_132_; lean_object* v_auxDeclNGen_133_; lean_object* v_cache_134_; lean_object* v_messages_135_; lean_object* v_infoState_136_; lean_object* v_snapshotTasks_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_167_; 
v___x_128_ = lean_st_ref_take(v___y_120_);
v_traceState_129_ = lean_ctor_get(v___x_128_, 4);
v_env_130_ = lean_ctor_get(v___x_128_, 0);
v_nextMacroScope_131_ = lean_ctor_get(v___x_128_, 1);
v_ngen_132_ = lean_ctor_get(v___x_128_, 2);
v_auxDeclNGen_133_ = lean_ctor_get(v___x_128_, 3);
v_cache_134_ = lean_ctor_get(v___x_128_, 5);
v_messages_135_ = lean_ctor_get(v___x_128_, 6);
v_infoState_136_ = lean_ctor_get(v___x_128_, 7);
v_snapshotTasks_137_ = lean_ctor_get(v___x_128_, 8);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_167_ == 0)
{
v___x_139_ = v___x_128_;
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snapshotTasks_137_);
lean_inc(v_infoState_136_);
lean_inc(v_messages_135_);
lean_inc(v_cache_134_);
lean_inc(v_traceState_129_);
lean_inc(v_auxDeclNGen_133_);
lean_inc(v_ngen_132_);
lean_inc(v_nextMacroScope_131_);
lean_inc(v_env_130_);
lean_dec(v___x_128_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint64_t v_tid_141_; lean_object* v_traces_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_166_; 
v_tid_141_ = lean_ctor_get_uint64(v_traceState_129_, sizeof(void*)*1);
v_traces_142_ = lean_ctor_get(v_traceState_129_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_traceState_129_);
if (v_isSharedCheck_166_ == 0)
{
v___x_144_ = v_traceState_129_;
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_traces_142_);
lean_dec(v_traceState_129_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; double v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
v___x_148_ = 0;
v___x_149_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_150_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_150_, 0, v_cls_115_);
lean_ctor_set(v___x_150_, 1, v___x_146_);
lean_ctor_set(v___x_150_, 2, v___x_149_);
lean_ctor_set_float(v___x_150_, sizeof(void*)*3, v___x_147_);
lean_ctor_set_float(v___x_150_, sizeof(void*)*3 + 8, v___x_147_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*3 + 16, v___x_148_);
v___x_151_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__2));
v___x_152_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v_a_124_);
lean_ctor_set(v___x_152_, 2, v___x_151_);
lean_inc(v_ref_122_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_ref_122_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = l_Lean_PersistentArray_push___redArg(v_traces_142_, v___x_153_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_154_);
v___x_156_ = v___x_144_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_154_);
lean_ctor_set_uint64(v_reuseFailAlloc_165_, sizeof(void*)*1, v_tid_141_);
v___x_156_ = v_reuseFailAlloc_165_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_158_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 4, v___x_156_);
v___x_158_ = v___x_139_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_env_130_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_nextMacroScope_131_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_ngen_132_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_auxDeclNGen_133_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_164_, 5, v_cache_134_);
lean_ctor_set(v_reuseFailAlloc_164_, 6, v_messages_135_);
lean_ctor_set(v_reuseFailAlloc_164_, 7, v_infoState_136_);
lean_ctor_set(v_reuseFailAlloc_164_, 8, v_snapshotTasks_137_);
v___x_158_ = v_reuseFailAlloc_164_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = lean_st_ref_put(v___y_120_, v___x_158_);
v___x_160_ = lean_box(0);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_160_);
v___x_162_ = v___x_126_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___boxed(lean_object* v_cls_169_, lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_169_, v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
v___x_189_ = l_Lean_Name_append(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__7));
v___x_192_ = l_Lean_stringToMessageData(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed(lean_object* v_a_199_, lean_object* v___x_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_k_203_, lean_object* v_tail_204_, lean_object* v_a_205_, lean_object* v_inst_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(v_a_199_, v___x_200_, v_a_201_, v_a_202_, v_k_203_, v_tail_204_, v_a_205_, v_inst_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___x_200_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(lean_object* v_k_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
if (lean_obj_tag(v_a_216_) == 0)
{
lean_object* v___x_227_; 
lean_dec(v_a_217_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_224_);
lean_inc(v_a_223_);
lean_inc_ref(v_a_222_);
lean_inc(v_a_221_);
lean_inc_ref(v_a_220_);
v___x_227_ = lean_apply_9(v_k_215_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, lean_box(0));
return v___x_227_;
}
else
{
lean_object* v_head_228_; lean_object* v_tail_229_; lean_object* v___y_231_; uint8_t v___y_232_; lean_object* v___y_237_; lean_object* v_a_238_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_head_228_ = lean_ctor_get(v_a_216_, 0);
lean_inc(v_head_228_);
v_tail_229_ = lean_ctor_get(v_a_216_, 1);
lean_inc(v_tail_229_);
lean_dec_ref_known(v_a_216_, 2);
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
v___x_244_ = lean_array_push(v___x_243_, v_head_228_);
v___x_245_ = l_Lean_Meta_mkAppM(v___x_241_, v___x_244_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_n(v_a_246_, 2);
lean_dec_ref_known(v___x_245_, 1);
v___x_247_ = 0;
v___x_248_ = l_Lean_Meta_check(v_a_246_, v___x_247_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref_known(v___x_248_, 1);
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3));
v___x_250_ = l_Lean_Core_mkFreshUserName(v___x_249_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___f_252_; uint8_t v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
lean_inc(v_a_246_);
lean_inc(v_tail_229_);
lean_inc_ref(v_k_215_);
lean_inc(v_a_219_);
lean_inc_ref(v_a_218_);
lean_inc(v_a_217_);
v___f_252_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed), 15, 7);
lean_closure_set(v___f_252_, 0, v_a_217_);
lean_closure_set(v___f_252_, 1, v___x_242_);
lean_closure_set(v___f_252_, 2, v_a_218_);
lean_closure_set(v___f_252_, 3, v_a_219_);
lean_closure_set(v___f_252_, 4, v_k_215_);
lean_closure_set(v___f_252_, 5, v_tail_229_);
lean_closure_set(v___f_252_, 6, v_a_246_);
v___x_253_ = 3;
v___x_254_ = 0;
v___x_255_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_a_251_, v___x_253_, v_a_246_, v___f_252_, v___x_254_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_dec(v_tail_229_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_k_215_);
return v___x_255_;
}
else
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
v___y_237_ = v___x_255_;
v_a_238_ = v_a_256_;
goto v___jp_236_;
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec(v_a_246_);
v_a_257_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_250_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_250_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
lean_inc(v_a_257_);
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
v___y_237_ = v___x_262_;
v_a_238_ = v_a_257_;
goto v___jp_236_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_a_246_);
v_a_265_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_248_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_248_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
lean_inc(v_a_265_);
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
v___y_237_ = v___x_270_;
v_a_238_ = v_a_265_;
goto v___jp_236_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_245_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_245_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
lean_inc(v_a_273_);
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
v___y_237_ = v___x_278_;
v_a_238_ = v_a_273_;
goto v___jp_236_;
}
}
}
v___jp_230_:
{
if (v___y_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec_ref(v___y_231_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_a_217_, v___x_233_);
lean_dec(v_a_217_);
v_a_216_ = v_tail_229_;
v_a_217_ = v___x_234_;
goto _start;
}
else
{
lean_dec(v_tail_229_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_k_215_);
return v___y_231_;
}
}
v___jp_236_:
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_Exception_isInterrupt(v_a_238_);
if (v___x_239_ == 0)
{
uint8_t v___x_240_; 
v___x_240_ = l_Lean_Exception_isRuntime(v_a_238_);
v___y_231_ = v___y_237_;
v___y_232_ = v___x_240_;
goto v___jp_230_;
}
else
{
lean_dec_ref(v_a_238_);
v___y_231_ = v___y_237_;
v___y_232_ = v___x_239_;
goto v___jp_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(lean_object* v_a_281_, lean_object* v___x_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_k_285_, lean_object* v_tail_286_, lean_object* v_a_287_, lean_object* v_inst_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v_options_308_; uint8_t v_hasTrace_309_; 
v_options_308_ = lean_ctor_get(v___y_293_, 2);
v_hasTrace_309_ = lean_ctor_get_uint8(v_options_308_, sizeof(void*)*1);
if (v_hasTrace_309_ == 0)
{
lean_dec_ref(v_a_287_);
v___y_297_ = v___y_289_;
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
v___y_302_ = v___y_294_;
goto v___jp_296_;
}
else
{
lean_object* v_inheritedTraceOptions_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_inheritedTraceOptions_310_ = lean_ctor_get(v___y_293_, 13);
v___x_311_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_312_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_313_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_310_, v_options_308_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec_ref(v_a_287_);
v___y_297_ = v___y_289_;
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
v___y_302_ = v___y_294_;
goto v___jp_296_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8);
v___x_315_ = l_Lean_MessageData_ofExpr(v_a_287_);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_311_, v___x_316_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_dec_ref_known(v___x_317_, 1);
v___y_297_ = v___y_289_;
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
v___y_302_ = v___y_294_;
goto v___jp_296_;
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v_inst_288_);
lean_dec(v_tail_286_);
lean_dec_ref(v_k_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_281_);
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
v___jp_296_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_303_ = lean_nat_add(v_a_281_, v___x_282_);
lean_inc_ref(v_inst_288_);
v___x_304_ = lean_array_push(v_a_283_, v_inst_288_);
v___x_305_ = l_Lean_Expr_fvarId_x21(v_inst_288_);
lean_dec_ref(v_inst_288_);
v___x_306_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_305_, v_a_281_, v_a_284_);
v___x_307_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_285_, v_tail_286_, v___x_303_, v___x_304_, v___x_306_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___boxed(lean_object* v_k_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(lean_object* v_00_u03b1_339_, lean_object* v_k_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___boxed(lean_object* v_00_u03b1_353_, lean_object* v_k_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(v_00_u03b1_353_, v_k_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(lean_object* v_cls_367_, lean_object* v_msg_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_367_, v_msg_368_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___boxed(lean_object* v_cls_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(v_cls_377_, v_msg_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(uint8_t v_addHypotheses_389_, lean_object* v_xs_390_, lean_object* v_k_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
if (v_addHypotheses_389_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec_ref(v_xs_390_);
v___x_399_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_400_ = lean_box(1);
lean_inc(v_a_397_);
lean_inc_ref(v_a_396_);
lean_inc(v_a_395_);
lean_inc_ref(v_a_394_);
lean_inc(v_a_393_);
lean_inc_ref(v_a_392_);
v___x_401_ = lean_apply_9(v_k_391_, v___x_399_, v___x_400_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, lean_box(0));
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_402_ = lean_array_to_list(v_xs_390_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_405_ = lean_box(1);
v___x_406_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_391_, v___x_402_, v___x_403_, v___x_404_, v___x_405_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___boxed(lean_object* v_addHypotheses_407_, lean_object* v_xs_408_, lean_object* v_k_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_addHypotheses_boxed_417_; lean_object* v_res_418_; 
v_addHypotheses_boxed_417_ = lean_unbox(v_addHypotheses_407_);
v_res_418_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_boxed_417_, v_xs_408_, v_k_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(uint8_t v_addHypotheses_419_, lean_object* v_00_u03b1_420_, lean_object* v_xs_421_, lean_object* v_k_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_419_, v_xs_421_, v_k_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed(lean_object* v_addHypotheses_431_, lean_object* v_00_u03b1_432_, lean_object* v_xs_433_, lean_object* v_k_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
uint8_t v_addHypotheses_boxed_442_; lean_object* v_res_443_; 
v_addHypotheses_boxed_442_ = lean_unbox(v_addHypotheses_431_);
v_res_443_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(v_addHypotheses_boxed_442_, v_00_u03b1_432_, v_xs_433_, v_k_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(lean_object* v_k_444_, lean_object* v_v_445_, lean_object* v_t_446_){
_start:
{
if (lean_obj_tag(v_t_446_) == 0)
{
lean_object* v_size_447_; lean_object* v_k_448_; lean_object* v_v_449_; lean_object* v_l_450_; lean_object* v_r_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_732_; 
v_size_447_ = lean_ctor_get(v_t_446_, 0);
v_k_448_ = lean_ctor_get(v_t_446_, 1);
v_v_449_ = lean_ctor_get(v_t_446_, 2);
v_l_450_ = lean_ctor_get(v_t_446_, 3);
v_r_451_ = lean_ctor_get(v_t_446_, 4);
v_isSharedCheck_732_ = !lean_is_exclusive(v_t_446_);
if (v_isSharedCheck_732_ == 0)
{
v___x_453_ = v_t_446_;
v_isShared_454_ = v_isSharedCheck_732_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_r_451_);
lean_inc(v_l_450_);
lean_inc(v_v_449_);
lean_inc(v_k_448_);
lean_inc(v_size_447_);
lean_dec(v_t_446_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_732_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
uint8_t v___x_455_; 
v___x_455_ = lean_nat_dec_lt(v_k_444_, v_k_448_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = lean_nat_dec_eq(v_k_444_, v_k_448_);
if (v___x_456_ == 0)
{
lean_object* v_impl_457_; lean_object* v___x_458_; 
lean_dec(v_size_447_);
v_impl_457_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_444_, v_v_445_, v_r_451_);
v___x_458_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_450_) == 0)
{
lean_object* v_size_459_; lean_object* v_size_460_; lean_object* v_k_461_; lean_object* v_v_462_; lean_object* v_l_463_; lean_object* v_r_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_size_459_ = lean_ctor_get(v_l_450_, 0);
v_size_460_ = lean_ctor_get(v_impl_457_, 0);
lean_inc(v_size_460_);
v_k_461_ = lean_ctor_get(v_impl_457_, 1);
lean_inc(v_k_461_);
v_v_462_ = lean_ctor_get(v_impl_457_, 2);
lean_inc(v_v_462_);
v_l_463_ = lean_ctor_get(v_impl_457_, 3);
lean_inc(v_l_463_);
v_r_464_ = lean_ctor_get(v_impl_457_, 4);
lean_inc(v_r_464_);
v___x_465_ = lean_unsigned_to_nat(3u);
v___x_466_ = lean_nat_mul(v___x_465_, v_size_459_);
v___x_467_ = lean_nat_dec_lt(v___x_466_, v_size_460_);
lean_dec(v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
lean_dec(v_r_464_);
lean_dec(v_l_463_);
lean_dec(v_v_462_);
lean_dec(v_k_461_);
v___x_468_ = lean_nat_add(v___x_458_, v_size_459_);
v___x_469_ = lean_nat_add(v___x_468_, v_size_460_);
lean_dec(v_size_460_);
lean_dec(v___x_468_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_impl_457_);
lean_ctor_set(v___x_453_, 0, v___x_469_);
v___x_471_ = v___x_453_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v_l_450_);
lean_ctor_set(v_reuseFailAlloc_472_, 4, v_impl_457_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
else
{
lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_536_; 
v_isSharedCheck_536_ = !lean_is_exclusive(v_impl_457_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_537_ = lean_ctor_get(v_impl_457_, 4);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_impl_457_, 3);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_impl_457_, 2);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_impl_457_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_impl_457_, 0);
lean_dec(v_unused_541_);
v___x_474_ = v_impl_457_;
v_isShared_475_ = v_isSharedCheck_536_;
goto v_resetjp_473_;
}
else
{
lean_dec(v_impl_457_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_536_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_size_476_; lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v_l_479_; lean_object* v_r_480_; lean_object* v_size_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_size_476_ = lean_ctor_get(v_l_463_, 0);
v_k_477_ = lean_ctor_get(v_l_463_, 1);
v_v_478_ = lean_ctor_get(v_l_463_, 2);
v_l_479_ = lean_ctor_get(v_l_463_, 3);
v_r_480_ = lean_ctor_get(v_l_463_, 4);
v_size_481_ = lean_ctor_get(v_r_464_, 0);
v___x_482_ = lean_unsigned_to_nat(2u);
v___x_483_ = lean_nat_mul(v___x_482_, v_size_481_);
v___x_484_ = lean_nat_dec_lt(v_size_476_, v___x_483_);
lean_dec(v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_512_; 
lean_inc(v_r_480_);
lean_inc(v_l_479_);
lean_inc(v_v_478_);
lean_inc(v_k_477_);
v_isSharedCheck_512_ = !lean_is_exclusive(v_l_463_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; 
v_unused_513_ = lean_ctor_get(v_l_463_, 4);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_l_463_, 3);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_l_463_, 2);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_l_463_, 1);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_l_463_, 0);
lean_dec(v_unused_517_);
v___x_486_ = v_l_463_;
v_isShared_487_ = v_isSharedCheck_512_;
goto v_resetjp_485_;
}
else
{
lean_dec(v_l_463_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_512_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_502_; 
v___x_488_ = lean_nat_add(v___x_458_, v_size_459_);
v___x_489_ = lean_nat_add(v___x_488_, v_size_460_);
lean_dec(v_size_460_);
if (lean_obj_tag(v_l_479_) == 0)
{
lean_object* v_size_510_; 
v_size_510_ = lean_ctor_get(v_l_479_, 0);
lean_inc(v_size_510_);
v___y_502_ = v_size_510_;
goto v___jp_501_;
}
else
{
lean_object* v___x_511_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___y_502_ = v___x_511_;
goto v___jp_501_;
}
v___jp_490_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_nat_add(v___y_491_, v___y_493_);
lean_dec(v___y_493_);
lean_dec(v___y_491_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 4, v_r_464_);
lean_ctor_set(v___x_486_, 3, v_r_480_);
lean_ctor_set(v___x_486_, 2, v_v_462_);
lean_ctor_set(v___x_486_, 1, v_k_461_);
lean_ctor_set(v___x_486_, 0, v___x_494_);
v___x_496_ = v___x_486_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_k_461_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_v_462_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_r_480_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_r_464_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 4, v___x_496_);
lean_ctor_set(v___x_474_, 3, v___y_492_);
lean_ctor_set(v___x_474_, 2, v_v_478_);
lean_ctor_set(v___x_474_, 1, v_k_477_);
lean_ctor_set(v___x_474_, 0, v___x_489_);
v___x_498_ = v___x_474_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v___y_492_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
v___jp_501_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_nat_add(v___x_488_, v___y_502_);
lean_dec(v___y_502_);
lean_dec(v___x_488_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_l_479_);
lean_ctor_set(v___x_453_, 0, v___x_503_);
v___x_505_ = v___x_453_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_l_450_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_l_479_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_nat_add(v___x_458_, v_size_481_);
if (lean_obj_tag(v_r_480_) == 0)
{
lean_object* v_size_507_; 
v_size_507_ = lean_ctor_get(v_r_480_, 0);
lean_inc(v_size_507_);
v___y_491_ = v___x_506_;
v___y_492_ = v___x_505_;
v___y_493_ = v_size_507_;
goto v___jp_490_;
}
else
{
lean_object* v___x_508_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___y_491_ = v___x_506_;
v___y_492_ = v___x_505_;
v___y_493_ = v___x_508_;
goto v___jp_490_;
}
}
}
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
lean_del_object(v___x_453_);
v___x_518_ = lean_nat_add(v___x_458_, v_size_459_);
v___x_519_ = lean_nat_add(v___x_518_, v_size_460_);
lean_dec(v_size_460_);
v___x_520_ = lean_nat_add(v___x_518_, v_size_476_);
lean_dec(v___x_518_);
lean_inc_ref(v_l_450_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 4, v_l_463_);
lean_ctor_set(v___x_474_, 3, v_l_450_);
lean_ctor_set(v___x_474_, 2, v_v_449_);
lean_ctor_set(v___x_474_, 1, v_k_448_);
lean_ctor_set(v___x_474_, 0, v___x_520_);
v___x_522_ = v___x_474_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_l_450_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_l_463_);
v___x_522_ = v_reuseFailAlloc_535_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_isSharedCheck_529_ = !lean_is_exclusive(v_l_450_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_530_ = lean_ctor_get(v_l_450_, 4);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_l_450_, 3);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_l_450_, 2);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_l_450_, 1);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_l_450_, 0);
lean_dec(v_unused_534_);
v___x_524_ = v_l_450_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_dec(v_l_450_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v_r_464_);
lean_ctor_set(v___x_524_, 3, v___x_522_);
lean_ctor_set(v___x_524_, 2, v_v_462_);
lean_ctor_set(v___x_524_, 1, v_k_461_);
lean_ctor_set(v___x_524_, 0, v___x_519_);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_k_461_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_v_462_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v_r_464_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_542_; 
v_l_542_ = lean_ctor_get(v_impl_457_, 3);
lean_inc(v_l_542_);
if (lean_obj_tag(v_l_542_) == 0)
{
lean_object* v_r_543_; lean_object* v_k_544_; lean_object* v_v_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_568_; 
v_r_543_ = lean_ctor_get(v_impl_457_, 4);
v_k_544_ = lean_ctor_get(v_impl_457_, 1);
v_v_545_ = lean_ctor_get(v_impl_457_, 2);
v_isSharedCheck_568_ = !lean_is_exclusive(v_impl_457_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_569_ = lean_ctor_get(v_impl_457_, 3);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_impl_457_, 0);
lean_dec(v_unused_570_);
v___x_547_ = v_impl_457_;
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_r_543_);
lean_inc(v_v_545_);
lean_inc(v_k_544_);
lean_dec(v_impl_457_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_k_549_; lean_object* v_v_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_564_; 
v_k_549_ = lean_ctor_get(v_l_542_, 1);
v_v_550_ = lean_ctor_get(v_l_542_, 2);
v_isSharedCheck_564_ = !lean_is_exclusive(v_l_542_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_565_ = lean_ctor_get(v_l_542_, 4);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_542_, 3);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_542_, 0);
lean_dec(v_unused_567_);
v___x_552_ = v_l_542_;
v_isShared_553_ = v_isSharedCheck_564_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_v_550_);
lean_inc(v_k_549_);
lean_dec(v_l_542_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_564_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_543_, 2);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 4, v_r_543_);
lean_ctor_set(v___x_552_, 3, v_r_543_);
lean_ctor_set(v___x_552_, 2, v_v_449_);
lean_ctor_set(v___x_552_, 1, v_k_448_);
lean_ctor_set(v___x_552_, 0, v___x_458_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_r_543_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_r_543_);
v___x_556_ = v_reuseFailAlloc_563_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
lean_inc(v_r_543_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 3, v_r_543_);
lean_ctor_set(v___x_547_, 0, v___x_458_);
v___x_558_ = v___x_547_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_k_544_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_v_545_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_r_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_r_543_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v___x_558_);
lean_ctor_set(v___x_453_, 3, v___x_556_);
lean_ctor_set(v___x_453_, 2, v_v_550_);
lean_ctor_set(v___x_453_, 1, v_k_549_);
lean_ctor_set(v___x_453_, 0, v___x_554_);
v___x_560_ = v___x_453_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_549_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_550_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
else
{
lean_object* v_r_571_; 
v_r_571_ = lean_ctor_get(v_impl_457_, 4);
lean_inc(v_r_571_);
if (lean_obj_tag(v_r_571_) == 0)
{
lean_object* v_k_572_; lean_object* v_v_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_584_; 
v_k_572_ = lean_ctor_get(v_impl_457_, 1);
v_v_573_ = lean_ctor_get(v_impl_457_, 2);
v_isSharedCheck_584_ = !lean_is_exclusive(v_impl_457_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_585_ = lean_ctor_get(v_impl_457_, 4);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_impl_457_, 3);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_impl_457_, 0);
lean_dec(v_unused_587_);
v___x_575_ = v_impl_457_;
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_v_573_);
lean_inc(v_k_572_);
lean_dec(v_impl_457_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(3u);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 4, v_l_542_);
lean_ctor_set(v___x_575_, 2, v_v_449_);
lean_ctor_set(v___x_575_, 1, v_k_448_);
lean_ctor_set(v___x_575_, 0, v___x_458_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_l_542_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_l_542_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_r_571_);
lean_ctor_set(v___x_453_, 3, v___x_579_);
lean_ctor_set(v___x_453_, 2, v_v_573_);
lean_ctor_set(v___x_453_, 1, v_k_572_);
lean_ctor_set(v___x_453_, 0, v___x_577_);
v___x_581_ = v___x_453_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_k_572_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_v_573_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v_r_571_);
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
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(2u);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_impl_457_);
lean_ctor_set(v___x_453_, 3, v_r_571_);
lean_ctor_set(v___x_453_, 0, v___x_588_);
v___x_590_ = v___x_453_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_r_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_impl_457_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
else
{
lean_object* v___x_593_; 
lean_dec(v_v_449_);
lean_dec(v_k_448_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 2, v_v_445_);
lean_ctor_set(v___x_453_, 1, v_k_444_);
v___x_593_ = v___x_453_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_size_447_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_444_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_445_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_l_450_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_r_451_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_impl_595_; lean_object* v___x_596_; 
lean_dec(v_size_447_);
v_impl_595_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_444_, v_v_445_, v_l_450_);
v___x_596_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_451_) == 0)
{
lean_object* v_size_597_; lean_object* v_size_598_; lean_object* v_k_599_; lean_object* v_v_600_; lean_object* v_l_601_; lean_object* v_r_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_size_597_ = lean_ctor_get(v_r_451_, 0);
v_size_598_ = lean_ctor_get(v_impl_595_, 0);
lean_inc(v_size_598_);
v_k_599_ = lean_ctor_get(v_impl_595_, 1);
lean_inc(v_k_599_);
v_v_600_ = lean_ctor_get(v_impl_595_, 2);
lean_inc(v_v_600_);
v_l_601_ = lean_ctor_get(v_impl_595_, 3);
lean_inc(v_l_601_);
v_r_602_ = lean_ctor_get(v_impl_595_, 4);
lean_inc(v_r_602_);
v___x_603_ = lean_unsigned_to_nat(3u);
v___x_604_ = lean_nat_mul(v___x_603_, v_size_597_);
v___x_605_ = lean_nat_dec_lt(v___x_604_, v_size_598_);
lean_dec(v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
lean_dec(v_r_602_);
lean_dec(v_l_601_);
lean_dec(v_v_600_);
lean_dec(v_k_599_);
v___x_606_ = lean_nat_add(v___x_596_, v_size_598_);
lean_dec(v_size_598_);
v___x_607_ = lean_nat_add(v___x_606_, v_size_597_);
lean_dec(v___x_606_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 3, v_impl_595_);
lean_ctor_set(v___x_453_, 0, v___x_607_);
v___x_609_ = v___x_453_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_impl_595_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_r_451_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_676_; 
v_isSharedCheck_676_ = !lean_is_exclusive(v_impl_595_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; 
v_unused_677_ = lean_ctor_get(v_impl_595_, 4);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_impl_595_, 3);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_impl_595_, 2);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_impl_595_, 1);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_impl_595_, 0);
lean_dec(v_unused_681_);
v___x_612_ = v_impl_595_;
v_isShared_613_ = v_isSharedCheck_676_;
goto v_resetjp_611_;
}
else
{
lean_dec(v_impl_595_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_676_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_size_614_; lean_object* v_size_615_; lean_object* v_k_616_; lean_object* v_v_617_; lean_object* v_l_618_; lean_object* v_r_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_size_614_ = lean_ctor_get(v_l_601_, 0);
v_size_615_ = lean_ctor_get(v_r_602_, 0);
v_k_616_ = lean_ctor_get(v_r_602_, 1);
v_v_617_ = lean_ctor_get(v_r_602_, 2);
v_l_618_ = lean_ctor_get(v_r_602_, 3);
v_r_619_ = lean_ctor_get(v_r_602_, 4);
v___x_620_ = lean_unsigned_to_nat(2u);
v___x_621_ = lean_nat_mul(v___x_620_, v_size_614_);
v___x_622_ = lean_nat_dec_lt(v_size_615_, v___x_621_);
lean_dec(v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_651_; 
lean_inc(v_r_619_);
lean_inc(v_l_618_);
lean_inc(v_v_617_);
lean_inc(v_k_616_);
v_isSharedCheck_651_ = !lean_is_exclusive(v_r_602_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_652_ = lean_ctor_get(v_r_602_, 4);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_r_602_, 3);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_r_602_, 2);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_r_602_, 1);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_r_602_, 0);
lean_dec(v_unused_656_);
v___x_624_ = v_r_602_;
v_isShared_625_ = v_isSharedCheck_651_;
goto v_resetjp_623_;
}
else
{
lean_dec(v_r_602_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_651_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___x_639_; lean_object* v___y_641_; 
v___x_626_ = lean_nat_add(v___x_596_, v_size_598_);
lean_dec(v_size_598_);
v___x_627_ = lean_nat_add(v___x_626_, v_size_597_);
lean_dec(v___x_626_);
v___x_639_ = lean_nat_add(v___x_596_, v_size_614_);
if (lean_obj_tag(v_l_618_) == 0)
{
lean_object* v_size_649_; 
v_size_649_ = lean_ctor_get(v_l_618_, 0);
lean_inc(v_size_649_);
v___y_641_ = v_size_649_;
goto v___jp_640_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___y_641_ = v___x_650_;
goto v___jp_640_;
}
v___jp_628_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = lean_nat_add(v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec(v___y_630_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_r_451_);
lean_ctor_set(v___x_624_, 3, v_r_619_);
lean_ctor_set(v___x_624_, 2, v_v_449_);
lean_ctor_set(v___x_624_, 1, v_k_448_);
lean_ctor_set(v___x_624_, 0, v___x_632_);
v___x_634_ = v___x_624_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_r_619_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_r_451_);
v___x_634_ = v_reuseFailAlloc_638_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 4, v___x_634_);
lean_ctor_set(v___x_612_, 3, v___y_629_);
lean_ctor_set(v___x_612_, 2, v_v_617_);
lean_ctor_set(v___x_612_, 1, v_k_616_);
lean_ctor_set(v___x_612_, 0, v___x_627_);
v___x_636_ = v___x_612_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_616_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v___y_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_nat_add(v___x_639_, v___y_641_);
lean_dec(v___y_641_);
lean_dec(v___x_639_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_l_618_);
lean_ctor_set(v___x_453_, 3, v_l_601_);
lean_ctor_set(v___x_453_, 2, v_v_600_);
lean_ctor_set(v___x_453_, 1, v_k_599_);
lean_ctor_set(v___x_453_, 0, v___x_642_);
v___x_644_ = v___x_453_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_599_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_600_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_l_601_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_l_618_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_nat_add(v___x_596_, v_size_597_);
if (lean_obj_tag(v_r_619_) == 0)
{
lean_object* v_size_646_; 
v_size_646_ = lean_ctor_get(v_r_619_, 0);
lean_inc(v_size_646_);
v___y_629_ = v___x_644_;
v___y_630_ = v___x_645_;
v___y_631_ = v_size_646_;
goto v___jp_628_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___y_629_ = v___x_644_;
v___y_630_ = v___x_645_;
v___y_631_ = v___x_647_;
goto v___jp_628_;
}
}
}
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
lean_del_object(v___x_453_);
v___x_657_ = lean_nat_add(v___x_596_, v_size_598_);
lean_dec(v_size_598_);
v___x_658_ = lean_nat_add(v___x_657_, v_size_597_);
lean_dec(v___x_657_);
v___x_659_ = lean_nat_add(v___x_596_, v_size_597_);
v___x_660_ = lean_nat_add(v___x_659_, v_size_615_);
lean_dec(v___x_659_);
lean_inc_ref(v_r_451_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 4, v_r_451_);
lean_ctor_set(v___x_612_, 3, v_r_602_);
lean_ctor_set(v___x_612_, 2, v_v_449_);
lean_ctor_set(v___x_612_, 1, v_k_448_);
lean_ctor_set(v___x_612_, 0, v___x_660_);
v___x_662_ = v___x_612_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_r_602_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_r_451_);
v___x_662_ = v_reuseFailAlloc_675_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_isSharedCheck_669_ = !lean_is_exclusive(v_r_451_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; lean_object* v_unused_673_; lean_object* v_unused_674_; 
v_unused_670_ = lean_ctor_get(v_r_451_, 4);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_r_451_, 3);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_r_451_, 2);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_r_451_, 1);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_r_451_, 0);
lean_dec(v_unused_674_);
v___x_664_ = v_r_451_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_dec(v_r_451_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v___x_662_);
lean_ctor_set(v___x_664_, 3, v_l_601_);
lean_ctor_set(v___x_664_, 2, v_v_600_);
lean_ctor_set(v___x_664_, 1, v_k_599_);
lean_ctor_set(v___x_664_, 0, v___x_658_);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_599_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_600_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_l_601_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v___x_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_682_; 
v_l_682_ = lean_ctor_get(v_impl_595_, 3);
lean_inc(v_l_682_);
if (lean_obj_tag(v_l_682_) == 0)
{
lean_object* v_r_683_; lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_696_; 
v_r_683_ = lean_ctor_get(v_impl_595_, 4);
v_k_684_ = lean_ctor_get(v_impl_595_, 1);
v_v_685_ = lean_ctor_get(v_impl_595_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_impl_595_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; 
v_unused_697_ = lean_ctor_get(v_impl_595_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_impl_595_, 0);
lean_dec(v_unused_698_);
v___x_687_ = v_impl_595_;
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_r_683_);
lean_inc(v_v_685_);
lean_inc(v_k_684_);
lean_dec(v_impl_595_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_683_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 3, v_r_683_);
lean_ctor_set(v___x_687_, 2, v_v_449_);
lean_ctor_set(v___x_687_, 1, v_k_448_);
lean_ctor_set(v___x_687_, 0, v___x_596_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_r_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_r_683_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v___x_691_);
lean_ctor_set(v___x_453_, 3, v_l_682_);
lean_ctor_set(v___x_453_, 2, v_v_685_);
lean_ctor_set(v___x_453_, 1, v_k_684_);
lean_ctor_set(v___x_453_, 0, v___x_689_);
v___x_693_ = v___x_453_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_r_699_; 
v_r_699_ = lean_ctor_get(v_impl_595_, 4);
lean_inc(v_r_699_);
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_700_; lean_object* v_v_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_724_; 
v_k_700_ = lean_ctor_get(v_impl_595_, 1);
v_v_701_ = lean_ctor_get(v_impl_595_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_impl_595_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; 
v_unused_725_ = lean_ctor_get(v_impl_595_, 4);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_impl_595_, 3);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_impl_595_, 0);
lean_dec(v_unused_727_);
v___x_703_ = v_impl_595_;
v_isShared_704_ = v_isSharedCheck_724_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_v_701_);
lean_inc(v_k_700_);
lean_dec(v_impl_595_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_724_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_k_705_; lean_object* v_v_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_720_; 
v_k_705_ = lean_ctor_get(v_r_699_, 1);
v_v_706_ = lean_ctor_get(v_r_699_, 2);
v_isSharedCheck_720_ = !lean_is_exclusive(v_r_699_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; 
v_unused_721_ = lean_ctor_get(v_r_699_, 4);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_r_699_, 3);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_r_699_, 0);
lean_dec(v_unused_723_);
v___x_708_ = v_r_699_;
v_isShared_709_ = v_isSharedCheck_720_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_v_706_);
lean_inc(v_k_705_);
lean_dec(v_r_699_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_720_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_unsigned_to_nat(3u);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v_l_682_);
lean_ctor_set(v___x_708_, 3, v_l_682_);
lean_ctor_set(v___x_708_, 2, v_v_701_);
lean_ctor_set(v___x_708_, 1, v_k_700_);
lean_ctor_set(v___x_708_, 0, v___x_596_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_700_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_701_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_l_682_);
v___x_712_ = v_reuseFailAlloc_719_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_l_682_);
lean_ctor_set(v___x_703_, 2, v_v_449_);
lean_ctor_set(v___x_703_, 1, v_k_448_);
lean_ctor_set(v___x_703_, 0, v___x_596_);
v___x_714_ = v___x_703_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_l_682_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v___x_714_);
lean_ctor_set(v___x_453_, 3, v___x_712_);
lean_ctor_set(v___x_453_, 2, v_v_706_);
lean_ctor_set(v___x_453_, 1, v_k_705_);
lean_ctor_set(v___x_453_, 0, v___x_710_);
v___x_716_ = v___x_453_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = lean_unsigned_to_nat(2u);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_r_699_);
lean_ctor_set(v___x_453_, 3, v_impl_595_);
lean_ctor_set(v___x_453_, 0, v___x_728_);
v___x_730_ = v___x_453_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_impl_595_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_r_699_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_k_444_);
lean_ctor_set(v___x_734_, 2, v_v_445_);
lean_ctor_set(v___x_734_, 3, v_t_446_);
lean_ctor_set(v___x_734_, 4, v_t_446_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(lean_object* v_t_735_, lean_object* v_k_736_){
_start:
{
if (lean_obj_tag(v_t_735_) == 0)
{
lean_object* v_k_737_; lean_object* v_v_738_; lean_object* v_l_739_; lean_object* v_r_740_; uint8_t v___x_741_; 
v_k_737_ = lean_ctor_get(v_t_735_, 1);
v_v_738_ = lean_ctor_get(v_t_735_, 2);
v_l_739_ = lean_ctor_get(v_t_735_, 3);
v_r_740_ = lean_ctor_get(v_t_735_, 4);
v___x_741_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_736_, v_k_737_);
switch(v___x_741_)
{
case 0:
{
v_t_735_ = v_l_739_;
goto _start;
}
case 1:
{
lean_object* v___x_743_; 
lean_inc(v_v_738_);
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v_v_738_);
return v___x_743_;
}
default: 
{
v_t_735_ = v_r_740_;
goto _start;
}
}
}
else
{
lean_object* v___x_745_; 
v___x_745_ = lean_box(0);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg___boxed(lean_object* v_t_746_, lean_object* v_k_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_746_, v_k_747_);
lean_dec(v_k_747_);
lean_dec(v_t_746_);
return v_res_748_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(lean_object* v_k_749_, lean_object* v_t_750_){
_start:
{
if (lean_obj_tag(v_t_750_) == 0)
{
lean_object* v_k_751_; lean_object* v_l_752_; lean_object* v_r_753_; uint8_t v___x_754_; 
v_k_751_ = lean_ctor_get(v_t_750_, 1);
v_l_752_ = lean_ctor_get(v_t_750_, 3);
v_r_753_ = lean_ctor_get(v_t_750_, 4);
v___x_754_ = lean_nat_dec_lt(v_k_749_, v_k_751_);
if (v___x_754_ == 0)
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_eq(v_k_749_, v_k_751_);
if (v___x_755_ == 0)
{
v_t_750_ = v_r_753_;
goto _start;
}
else
{
return v___x_755_;
}
}
else
{
v_t_750_ = v_l_752_;
goto _start;
}
}
else
{
uint8_t v___x_758_; 
v___x_758_ = 0;
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg___boxed(lean_object* v_k_759_, lean_object* v_t_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_759_, v_t_760_);
lean_dec(v_t_760_);
lean_dec(v_k_759_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(lean_object* v_localInst2Index_763_, lean_object* v_e_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_fvarId_767_; lean_object* v___x_768_; 
v_fvarId_767_ = l_Lean_Expr_fvarId_x21(v_e_764_);
v___x_768_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_localInst2Index_763_, v_fvarId_767_);
lean_dec(v_fvarId_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; 
v___x_769_ = lean_box(0);
return v___x_769_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___y_774_; uint8_t v___x_776_; 
v_val_770_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_768_, 1);
v___x_771_ = lean_st_ref_take(v___y_765_);
v___x_772_ = lean_box(0);
v___x_776_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_val_770_, v___x_771_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_val_770_, v___x_772_, v___x_771_);
v___y_774_ = v___x_777_;
goto v___jp_773_;
}
else
{
lean_dec(v_val_770_);
v___y_774_ = v___x_771_;
goto v___jp_773_;
}
v___jp_773_:
{
lean_object* v___x_775_; 
v___x_775_ = lean_st_ref_put(v___y_765_, v___y_774_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed(lean_object* v_localInst2Index_778_, lean_object* v_e_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(v_localInst2Index_778_, v_e_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v_e_779_);
lean_dec(v_localInst2Index_778_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_m_783_, lean_object* v_query_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_zero_788_; uint8_t v_isZero_789_; 
v_zero_788_ = lean_unsigned_to_nat(0u);
v_isZero_789_ = lean_nat_dec_eq(v_x_786_, v_zero_788_);
if (v_isZero_789_ == 1)
{
lean_dec(v_x_787_);
lean_dec(v_x_786_);
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_box(2);
return v___x_790_;
}
else
{
lean_object* v_val_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_val_791_ = lean_ctor_get(v_x_785_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v_x_785_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_val_791_);
lean_dec(v_x_785_);
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
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_val_791_);
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
lean_object* v_keyArray_799_; lean_object* v_valueArray_800_; lean_object* v___x_801_; uint8_t v_isSome_802_; 
v_keyArray_799_ = lean_ctor_get(v_m_783_, 1);
v_valueArray_800_ = lean_ctor_get(v_m_783_, 2);
v___x_801_ = lean_array_fget_borrowed(v_keyArray_799_, v_x_787_);
v_isSome_802_ = lean_noption_is_some(v___x_801_);
if (v_isSome_802_ == 0)
{
lean_dec(v_x_786_);
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_x_787_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_x_787_);
v_val_804_ = lean_ctor_get(v_x_785_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v_x_785_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_val_804_);
lean_dec(v_x_785_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_val_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_one_812_; lean_object* v_n_813_; lean_object* v___y_815_; 
v_one_812_ = lean_unsigned_to_nat(1u);
v_n_813_ = lean_nat_sub(v_x_786_, v_one_812_);
lean_dec(v_x_786_);
if (v_isSome_802_ == 0)
{
goto v___jp_821_;
}
else
{
lean_object* v___x_823_; uint8_t v_isSome_824_; 
v___x_823_ = lean_array_fget_borrowed(v_valueArray_800_, v_x_787_);
v_isSome_824_ = lean_noption_is_some(v___x_823_);
if (v_isSome_824_ == 0)
{
goto v___jp_821_;
}
else
{
lean_object* v_val_825_; uint8_t v___x_826_; 
lean_inc(v___x_801_);
v_val_825_ = lean_noption_get(v___x_801_);
v___x_826_ = lean_expr_eqv(v_val_825_, v_query_784_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
lean_dec(v_val_825_);
v___x_827_ = lean_array_get_size(v_keyArray_799_);
v___x_828_ = lean_nat_add(v_x_787_, v_one_812_);
lean_dec(v_x_787_);
v___x_829_ = lean_nat_dec_lt(v___x_828_, v___x_827_);
if (v___x_829_ == 0)
{
lean_dec(v___x_828_);
v_x_786_ = v_n_813_;
v_x_787_ = v_zero_788_;
goto _start;
}
else
{
v_x_786_ = v_n_813_;
v_x_787_ = v___x_828_;
goto _start;
}
}
else
{
lean_object* v_val_832_; lean_object* v___x_833_; 
lean_dec(v_n_813_);
lean_dec(v_x_785_);
lean_inc(v___x_823_);
v_val_832_ = lean_noption_get(v___x_823_);
v___x_833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_833_, 0, v_x_787_);
lean_ctor_set(v___x_833_, 1, v_val_825_);
lean_ctor_set(v___x_833_, 2, v_val_832_);
return v___x_833_;
}
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_816_ = lean_array_get_size(v_keyArray_799_);
v___x_817_ = lean_nat_add(v_x_787_, v_one_812_);
lean_dec(v_x_787_);
v___x_818_ = lean_nat_dec_lt(v___x_817_, v___x_816_);
if (v___x_818_ == 0)
{
lean_dec(v___x_817_);
v_x_785_ = v___y_815_;
v_x_786_ = v_n_813_;
v_x_787_ = v_zero_788_;
goto _start;
}
else
{
v_x_785_ = v___y_815_;
v_x_786_ = v_n_813_;
v_x_787_ = v___x_817_;
goto _start;
}
}
v___jp_821_:
{
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v___x_822_; 
lean_inc(v_x_787_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_x_787_);
v___y_815_ = v___x_822_;
goto v___jp_814_;
}
else
{
v___y_815_ = v_x_785_;
goto v___jp_814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_m_834_, lean_object* v_query_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_m_834_, v_query_835_, v_x_836_, v_x_837_, v_x_838_);
lean_dec_ref(v_query_835_);
lean_dec_ref(v_m_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(lean_object* v_m_840_, lean_object* v_query_841_){
_start:
{
lean_object* v_keyArray_842_; lean_object* v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v_fold_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_keyArray_842_ = lean_ctor_get(v_m_840_, 1);
v___x_843_ = lean_array_get_size(v_keyArray_842_);
v___x_844_ = l_Lean_Expr_hash(v_query_841_);
v___x_845_ = 32ULL;
v___x_846_ = lean_uint64_shift_right(v___x_844_, v___x_845_);
v_fold_847_ = lean_uint64_xor(v___x_844_, v___x_846_);
v___x_848_ = 16ULL;
v___x_849_ = lean_uint64_shift_right(v_fold_847_, v___x_848_);
v___x_850_ = lean_uint64_xor(v_fold_847_, v___x_849_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = lean_usize_of_nat(v___x_843_);
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_sub(v___x_852_, v___x_853_);
v___x_855_ = lean_usize_land(v___x_851_, v___x_854_);
v___x_856_ = lean_usize_to_nat(v___x_855_);
v___x_857_ = lean_box(0);
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_m_840_, v_query_841_, v___x_857_, v___x_843_, v___x_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_m_859_, lean_object* v_query_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_m_859_, v_query_860_);
lean_dec_ref(v_query_860_);
lean_dec_ref(v_m_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___redArg(lean_object* v_b_862_, lean_object* v_acc_863_, lean_object* v_i_864_){
_start:
{
lean_object* v___y_866_; lean_object* v_keyArray_874_; lean_object* v_valueArray_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_keyArray_874_ = lean_ctor_get(v_b_862_, 1);
v_valueArray_875_ = lean_ctor_get(v_b_862_, 2);
v___x_876_ = lean_array_get_size(v_keyArray_874_);
v___x_877_ = lean_nat_dec_lt(v_i_864_, v___x_876_);
if (v___x_877_ == 0)
{
lean_dec(v_i_864_);
return v_acc_863_;
}
else
{
lean_object* v___x_878_; uint8_t v_isSome_879_; 
v___x_878_ = lean_array_fget_borrowed(v_keyArray_874_, v_i_864_);
v_isSome_879_ = lean_noption_is_some(v___x_878_);
if (v_isSome_879_ == 0)
{
goto v___jp_870_;
}
else
{
lean_object* v___x_880_; uint8_t v_isSome_881_; 
v___x_880_ = lean_array_fget_borrowed(v_valueArray_875_, v_i_864_);
v_isSome_881_ = lean_noption_is_some(v___x_880_);
if (v_isSome_881_ == 0)
{
goto v___jp_870_;
}
else
{
lean_object* v_val_882_; lean_object* v_val_883_; lean_object* v_i_885_; lean_object* v___x_890_; 
lean_inc(v___x_878_);
v_val_882_ = lean_noption_get(v___x_878_);
lean_inc(v___x_880_);
v_val_883_ = lean_noption_get(v___x_880_);
v___x_890_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_acc_863_, v_val_882_);
switch(lean_obj_tag(v___x_890_))
{
case 0:
{
lean_object* v_index_891_; lean_object* v_size_892_; lean_object* v___x_893_; 
v_index_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_index_891_);
lean_dec_ref_known(v___x_890_, 3);
v_size_892_ = lean_ctor_get(v_acc_863_, 0);
lean_inc(v_size_892_);
v___x_893_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_863_, v_size_892_, v_index_891_, v_val_882_, v_val_883_);
lean_dec(v_index_891_);
v___y_866_ = v___x_893_;
goto v___jp_865_;
}
case 1:
{
lean_object* v_index_894_; 
v_index_894_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_index_894_);
lean_dec_ref_known(v___x_890_, 1);
v_i_885_ = v_index_894_;
goto v___jp_884_;
}
default: 
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_863_, v___x_895_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_index_897_; 
v_index_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_index_897_);
lean_dec_ref_known(v___x_896_, 1);
v_i_885_ = v_index_897_;
goto v___jp_884_;
}
else
{
lean_dec(v_val_883_);
lean_dec(v_val_882_);
v___y_866_ = v_acc_863_;
goto v___jp_865_;
}
}
}
v___jp_884_:
{
lean_object* v_size_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_size_886_ = lean_ctor_get(v_acc_863_, 0);
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_nat_add(v_size_886_, v___x_887_);
v___x_889_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_863_, v___x_888_, v_i_885_, v_val_882_, v_val_883_);
lean_dec(v_i_885_);
v___y_866_ = v___x_889_;
goto v___jp_865_;
}
}
}
}
v___jp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_i_864_, v___x_867_);
lean_dec(v_i_864_);
v_acc_863_ = v___y_866_;
v_i_864_ = v___x_868_;
goto _start;
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_i_864_, v___x_871_);
lean_dec(v_i_864_);
v_i_864_ = v___x_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___redArg___boxed(lean_object* v_b_898_, lean_object* v_acc_899_, lean_object* v_i_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___redArg(v_b_898_, v_acc_899_, v_i_900_);
lean_dec_ref(v_b_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___redArg(lean_object* v_init_902_, lean_object* v_b_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___redArg(v_b_903_, v_init_902_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_init_906_, lean_object* v_b_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___redArg(v_init_906_, v_b_907_);
lean_dec_ref(v_b_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg(lean_object* v_m_909_){
_start:
{
lean_object* v_keyArray_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_cellCount_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_target_917_; lean_object* v___x_918_; 
v_keyArray_910_ = lean_ctor_get(v_m_909_, 1);
v___x_911_ = lean_array_get_size(v_keyArray_910_);
v___x_912_ = lean_unsigned_to_nat(2u);
v_cellCount_913_ = lean_nat_mul(v___x_911_, v___x_912_);
v___x_914_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_913_);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_913_);
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_913_);
v_target_917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_917_, 0, v___x_914_);
lean_ctor_set(v_target_917_, 1, v___x_915_);
lean_ctor_set(v_target_917_, 2, v___x_916_);
v___x_918_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___redArg(v_target_917_, v_m_909_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_m_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg(v_m_919_);
lean_dec_ref(v_m_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_m_921_, lean_object* v_query_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_m_921_, v_query_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_index_924_; lean_object* v_key_925_; lean_object* v_value_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_index_924_ = lean_ctor_get(v___x_923_, 0);
v_key_925_ = lean_ctor_get(v___x_923_, 1);
v_value_926_ = lean_ctor_get(v___x_923_, 2);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_923_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_value_926_);
lean_inc(v_key_925_);
lean_inc(v_index_924_);
lean_dec(v___x_923_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_index_924_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_key_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_value_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_object* v___x_934_; 
lean_dec(v___x_923_);
v___x_934_ = lean_box(1);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_m_935_, lean_object* v_query_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_m_935_, v_query_936_);
lean_dec_ref(v_query_936_);
lean_dec_ref(v_m_935_);
return v_res_937_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(lean_object* v_m_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_m_938_, v_a_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
uint8_t v___x_941_; 
lean_dec_ref_known(v___x_940_, 3);
v___x_941_ = 1;
return v___x_941_;
}
else
{
uint8_t v___x_942_; 
v___x_942_ = 0;
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_m_943_, lean_object* v_a_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_943_, v_a_944_);
lean_dec_ref(v_a_944_);
lean_dec_ref(v_m_943_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(lean_object* v_e_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v_checked_951_; uint8_t v___x_952_; 
v___x_950_ = lean_st_ref_get(v_a_948_);
v_checked_951_ = lean_ctor_get(v___x_950_, 1);
lean_inc_ref(v_checked_951_);
lean_dec(v___x_950_);
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_checked_951_, v_e_947_);
lean_dec_ref(v_checked_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v_visited_954_; lean_object* v_checked_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1027_; 
v___x_953_ = lean_st_ref_take(v_a_948_);
v_visited_954_ = lean_ctor_get(v___x_953_, 0);
v_checked_955_ = lean_ctor_get(v___x_953_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_957_ = v___x_953_;
v_isShared_958_ = v_isSharedCheck_1027_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_checked_955_);
lean_inc(v_visited_954_);
lean_dec(v___x_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1027_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___y_960_; lean_object* v___x_965_; lean_object* v___y_967_; lean_object* v_i_968_; lean_object* v___y_974_; lean_object* v___y_984_; lean_object* v_i_985_; lean_object* v___x_1000_; 
v___x_965_ = lean_box(0);
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_checked_955_, v_e_947_);
switch(lean_obj_tag(v___x_1000_))
{
case 0:
{
lean_dec_ref_known(v___x_1000_, 3);
lean_dec_ref(v_e_947_);
v___y_960_ = v_checked_955_;
goto v___jp_959_;
}
case 1:
{
lean_object* v_index_1001_; lean_object* v_size_1002_; lean_object* v_keyArray_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_index_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_index_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v_size_1002_ = lean_ctor_get(v_checked_955_, 0);
v_keyArray_1003_ = lean_ctor_get(v_checked_955_, 1);
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_add(v_size_1002_, v___x_1004_);
v___x_1006_ = lean_array_get_size(v_keyArray_1003_);
v___x_1007_ = lean_nat_dec_lt(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec(v___x_1005_);
lean_dec(v_index_1001_);
goto v___jp_990_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1008_ = lean_unsigned_to_nat(4u);
v___x_1009_ = lean_nat_mul(v___x_1005_, v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(3u);
v___x_1011_ = lean_nat_mul(v___x_1006_, v___x_1010_);
v___x_1012_ = lean_nat_dec_le(v___x_1009_, v___x_1011_);
lean_dec(v___x_1011_);
lean_dec(v___x_1009_);
if (v___x_1012_ == 0)
{
lean_dec(v___x_1005_);
lean_dec(v_index_1001_);
goto v___jp_990_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Raw_setEntry___redArg(v_checked_955_, v___x_1005_, v_index_1001_, v_e_947_, v___x_965_);
lean_dec(v_index_1001_);
v___y_960_ = v___x_1013_;
goto v___jp_959_;
}
}
}
default: 
{
lean_object* v_size_1014_; lean_object* v_keyArray_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_size_1014_ = lean_ctor_get(v_checked_955_, 0);
v_keyArray_1015_ = lean_ctor_get(v_checked_955_, 1);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_size_1014_, v___x_1016_);
v___x_1018_ = lean_array_get_size(v_keyArray_1015_);
v___x_1019_ = lean_nat_dec_lt(v___x_1017_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec(v___x_1017_);
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg(v_checked_955_);
lean_dec_ref(v_checked_955_);
v___y_974_ = v___x_1020_;
goto v___jp_973_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1021_ = lean_unsigned_to_nat(4u);
v___x_1022_ = lean_nat_mul(v___x_1017_, v___x_1021_);
lean_dec(v___x_1017_);
v___x_1023_ = lean_unsigned_to_nat(3u);
v___x_1024_ = lean_nat_mul(v___x_1018_, v___x_1023_);
v___x_1025_ = lean_nat_dec_le(v___x_1022_, v___x_1024_);
lean_dec(v___x_1024_);
lean_dec(v___x_1022_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg(v_checked_955_);
lean_dec_ref(v_checked_955_);
v___y_974_ = v___x_1026_;
goto v___jp_973_;
}
else
{
v___y_974_ = v_checked_955_;
goto v___jp_973_;
}
}
}
}
v___jp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___y_960_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_visited_954_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___y_960_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = lean_st_ref_put(v_a_948_, v___x_962_);
return v___x_952_;
}
}
v___jp_966_:
{
lean_object* v_size_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_size_969_ = lean_ctor_get(v___y_967_, 0);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_add(v_size_969_, v___x_970_);
v___x_972_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_967_, v___x_971_, v_i_968_, v_e_947_, v___x_965_);
lean_dec(v_i_968_);
v___y_960_ = v___x_972_;
goto v___jp_959_;
}
v___jp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v___y_974_, v_e_947_);
switch(lean_obj_tag(v___x_975_))
{
case 0:
{
lean_object* v_index_976_; lean_object* v_size_977_; lean_object* v___x_978_; 
v_index_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_index_976_);
lean_dec_ref_known(v___x_975_, 3);
v_size_977_ = lean_ctor_get(v___y_974_, 0);
lean_inc(v_size_977_);
v___x_978_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_974_, v_size_977_, v_index_976_, v_e_947_, v___x_965_);
lean_dec(v_index_976_);
v___y_960_ = v___x_978_;
goto v___jp_959_;
}
case 1:
{
lean_object* v_index_979_; 
v_index_979_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_index_979_);
lean_dec_ref_known(v___x_975_, 1);
v___y_967_ = v___y_974_;
v_i_968_ = v_index_979_;
goto v___jp_966_;
}
default: 
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_974_, v___x_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_index_982_; 
v_index_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_index_982_);
lean_dec_ref_known(v___x_981_, 1);
v___y_967_ = v___y_974_;
v_i_968_ = v_index_982_;
goto v___jp_966_;
}
else
{
lean_dec_ref(v_e_947_);
v___y_960_ = v___y_974_;
goto v___jp_959_;
}
}
}
}
v___jp_983_:
{
lean_object* v_size_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_size_986_ = lean_ctor_get(v___y_984_, 0);
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_nat_add(v_size_986_, v___x_987_);
v___x_989_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_984_, v___x_988_, v_i_985_, v_e_947_, v___x_965_);
lean_dec(v_i_985_);
v___y_960_ = v___x_989_;
goto v___jp_959_;
}
v___jp_990_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg(v_checked_955_);
lean_dec_ref(v_checked_955_);
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v___x_991_, v_e_947_);
switch(lean_obj_tag(v___x_992_))
{
case 0:
{
lean_object* v_index_993_; lean_object* v_size_994_; lean_object* v___x_995_; 
v_index_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_index_993_);
lean_dec_ref_known(v___x_992_, 3);
v_size_994_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_size_994_);
v___x_995_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_991_, v_size_994_, v_index_993_, v_e_947_, v___x_965_);
lean_dec(v_index_993_);
v___y_960_ = v___x_995_;
goto v___jp_959_;
}
case 1:
{
lean_object* v_index_996_; 
v_index_996_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_index_996_);
lean_dec_ref_known(v___x_992_, 1);
v___y_984_ = v___x_991_;
v_i_985_ = v_index_996_;
goto v___jp_983_;
}
default: 
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_991_, v___x_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_index_999_; 
v_index_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_index_999_);
lean_dec_ref_known(v___x_998_, 1);
v___y_984_ = v___x_991_;
v_i_985_ = v_index_999_;
goto v___jp_983_;
}
else
{
lean_dec_ref(v_e_947_);
v___y_960_ = v___x_991_;
goto v___jp_959_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_947_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_e_1028_, lean_object* v_a_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_res_1031_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_1028_, v_a_1029_);
lean_dec(v_a_1029_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(lean_object* v_e_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v_visited_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; size_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1036_ = lean_st_ref_get(v_a_1034_);
v_visited_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_visited_1037_);
lean_dec(v___x_1036_);
v___x_1038_ = lean_ptr_addr(v_e_1033_);
v___x_1039_ = ((size_t)8191ULL);
v___x_1040_ = lean_usize_mod(v___x_1038_, v___x_1039_);
v___x_1041_ = lean_array_uget(v_visited_1037_, v___x_1040_);
lean_dec_ref(v_visited_1037_);
v___x_1042_ = lean_ptr_addr(v___x_1041_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_usize_dec_eq(v___x_1042_, v___x_1038_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v_visited_1045_; lean_object* v_checked_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1055_; 
v___x_1044_ = lean_st_ref_take(v_a_1034_);
v_visited_1045_ = lean_ctor_get(v___x_1044_, 0);
v_checked_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_checked_1046_);
lean_inc(v_visited_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = lean_array_uset(v_visited_1045_, v___x_1040_, v_e_1033_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_checked_1046_);
v___x_1052_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_st_ref_put(v_a_1034_, v___x_1052_);
return v___x_1043_;
}
}
}
else
{
lean_dec_ref(v_e_1033_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_e_1056_, lean_object* v_a_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_1056_, v_a_1057_);
lean_dec(v_a_1057_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(lean_object* v_p_1061_, lean_object* v_f_1062_, uint8_t v_stopWhenVisited_1063_, lean_object* v_e_1064_, lean_object* v_a_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___y_1069_; lean_object* v_d_1070_; lean_object* v_b_1071_; lean_object* v___y_1072_; lean_object* v___y_1076_; lean_object* v___y_1077_; uint8_t v___x_1097_; 
lean_inc_ref(v_e_1064_);
v___x_1097_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_1064_, v_a_1065_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
lean_inc_ref(v_p_1061_);
lean_inc_ref(v_e_1064_);
v___x_1098_ = lean_apply_1(v_p_1061_, v_e_1064_);
v___x_1099_ = lean_unbox(v___x_1098_);
if (v___x_1099_ == 0)
{
v___y_1076_ = v_a_1065_;
v___y_1077_ = v___y_1066_;
goto v___jp_1075_;
}
else
{
uint8_t v___x_1100_; 
lean_inc_ref(v_e_1064_);
v___x_1100_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_1064_, v_a_1065_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_inc_ref(v_f_1062_);
lean_inc(v___y_1066_);
lean_inc_ref(v_e_1064_);
v___x_1101_ = lean_apply_3(v_f_1062_, v_e_1064_, v___y_1066_, lean_box(0));
if (v_stopWhenVisited_1063_ == 0)
{
v___y_1076_ = v_a_1065_;
v___y_1077_ = v___y_1066_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1102_; 
lean_dec_ref(v_e_1064_);
lean_dec_ref(v_f_1062_);
lean_dec_ref(v_p_1061_);
v___x_1102_ = lean_box(0);
return v___x_1102_;
}
}
else
{
v___y_1076_ = v_a_1065_;
v___y_1077_ = v___y_1066_;
goto v___jp_1075_;
}
}
}
else
{
lean_object* v___x_1103_; 
lean_dec_ref(v_e_1064_);
lean_dec_ref(v_f_1062_);
lean_dec_ref(v_p_1061_);
v___x_1103_ = lean_box(0);
return v___x_1103_;
}
v___jp_1068_:
{
lean_object* v___x_1073_; 
lean_inc_ref(v_f_1062_);
lean_inc_ref(v_p_1061_);
v___x_1073_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1061_, v_f_1062_, v_stopWhenVisited_1063_, v_d_1070_, v___y_1072_, v___y_1069_);
v_e_1064_ = v_b_1071_;
v_a_1065_ = v___y_1072_;
v___y_1066_ = v___y_1069_;
goto _start;
}
v___jp_1075_:
{
switch(lean_obj_tag(v_e_1064_))
{
case 7:
{
lean_object* v_binderType_1078_; lean_object* v_body_1079_; 
v_binderType_1078_ = lean_ctor_get(v_e_1064_, 1);
lean_inc_ref(v_binderType_1078_);
v_body_1079_ = lean_ctor_get(v_e_1064_, 2);
lean_inc_ref(v_body_1079_);
lean_dec_ref_known(v_e_1064_, 3);
v___y_1069_ = v___y_1077_;
v_d_1070_ = v_binderType_1078_;
v_b_1071_ = v_body_1079_;
v___y_1072_ = v___y_1076_;
goto v___jp_1068_;
}
case 6:
{
lean_object* v_binderType_1080_; lean_object* v_body_1081_; 
v_binderType_1080_ = lean_ctor_get(v_e_1064_, 1);
lean_inc_ref(v_binderType_1080_);
v_body_1081_ = lean_ctor_get(v_e_1064_, 2);
lean_inc_ref(v_body_1081_);
lean_dec_ref_known(v_e_1064_, 3);
v___y_1069_ = v___y_1077_;
v_d_1070_ = v_binderType_1080_;
v_b_1071_ = v_body_1081_;
v___y_1072_ = v___y_1076_;
goto v___jp_1068_;
}
case 8:
{
lean_object* v_type_1082_; lean_object* v_value_1083_; lean_object* v_body_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_type_1082_ = lean_ctor_get(v_e_1064_, 1);
lean_inc_ref(v_type_1082_);
v_value_1083_ = lean_ctor_get(v_e_1064_, 2);
lean_inc_ref(v_value_1083_);
v_body_1084_ = lean_ctor_get(v_e_1064_, 3);
lean_inc_ref(v_body_1084_);
lean_dec_ref_known(v_e_1064_, 4);
lean_inc_ref_n(v_f_1062_, 2);
lean_inc_ref_n(v_p_1061_, 2);
v___x_1085_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1061_, v_f_1062_, v_stopWhenVisited_1063_, v_type_1082_, v___y_1076_, v___y_1077_);
v___x_1086_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1061_, v_f_1062_, v_stopWhenVisited_1063_, v_value_1083_, v___y_1076_, v___y_1077_);
v_e_1064_ = v_body_1084_;
v_a_1065_ = v___y_1076_;
v___y_1066_ = v___y_1077_;
goto _start;
}
case 5:
{
lean_object* v_fn_1088_; lean_object* v_arg_1089_; lean_object* v___x_1090_; 
v_fn_1088_ = lean_ctor_get(v_e_1064_, 0);
lean_inc_ref(v_fn_1088_);
v_arg_1089_ = lean_ctor_get(v_e_1064_, 1);
lean_inc_ref(v_arg_1089_);
lean_dec_ref_known(v_e_1064_, 2);
lean_inc_ref(v_f_1062_);
lean_inc_ref(v_p_1061_);
v___x_1090_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1061_, v_f_1062_, v_stopWhenVisited_1063_, v_fn_1088_, v___y_1076_, v___y_1077_);
v_e_1064_ = v_arg_1089_;
v_a_1065_ = v___y_1076_;
v___y_1066_ = v___y_1077_;
goto _start;
}
case 10:
{
lean_object* v_expr_1092_; 
v_expr_1092_ = lean_ctor_get(v_e_1064_, 1);
lean_inc_ref(v_expr_1092_);
lean_dec_ref_known(v_e_1064_, 2);
v_e_1064_ = v_expr_1092_;
v_a_1065_ = v___y_1076_;
v___y_1066_ = v___y_1077_;
goto _start;
}
case 11:
{
lean_object* v_struct_1094_; 
v_struct_1094_ = lean_ctor_get(v_e_1064_, 2);
lean_inc_ref(v_struct_1094_);
lean_dec_ref_known(v_e_1064_, 3);
v_e_1064_ = v_struct_1094_;
v_a_1065_ = v___y_1076_;
v___y_1066_ = v___y_1077_;
goto _start;
}
default: 
{
lean_object* v___x_1096_; 
lean_dec_ref(v_e_1064_);
lean_dec_ref(v_f_1062_);
lean_dec_ref(v_p_1061_);
v___x_1096_ = lean_box(0);
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg___boxed(lean_object* v_p_1104_, lean_object* v_f_1105_, lean_object* v_stopWhenVisited_1106_, lean_object* v_e_1107_, lean_object* v_a_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1111_; lean_object* v_res_1112_; 
v_stopWhenVisited_boxed_1111_ = lean_unbox(v_stopWhenVisited_1106_);
v_res_1112_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1104_, v_f_1105_, v_stopWhenVisited_boxed_1111_, v_e_1107_, v_a_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec(v_a_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(lean_object* v_p_1113_, lean_object* v_f_1114_, lean_object* v_e_1115_, uint8_t v_stopWhenVisited_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = l_Lean_ForEachExprWhere_initCache;
v___x_1120_ = lean_st_mk_ref(v___x_1119_);
v___x_1121_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1113_, v_f_1114_, v_stopWhenVisited_1116_, v_e_1115_, v___x_1120_, v___y_1117_);
v___x_1122_ = lean_st_ref_get(v___x_1120_);
lean_dec(v___x_1120_);
lean_dec(v___x_1122_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg___boxed(lean_object* v_p_1123_, lean_object* v_f_1124_, lean_object* v_e_1125_, lean_object* v_stopWhenVisited_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1129_; lean_object* v_res_1130_; 
v_stopWhenVisited_boxed_1129_ = lean_unbox(v_stopWhenVisited_1126_);
v_res_1130_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1123_, v_f_1124_, v_e_1125_, v_stopWhenVisited_boxed_1129_, v___y_1127_);
lean_dec(v___y_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(lean_object* v_usedInstIdxs_1132_, lean_object* v___f_1133_, lean_object* v_e_1134_, uint8_t v___x_1135_, lean_object* v_x_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1138_ = lean_st_mk_ref(v_usedInstIdxs_1132_);
v___x_1139_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0));
v___x_1140_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v___x_1139_, v___f_1133_, v_e_1134_, v___x_1135_, v___x_1138_);
v___x_1141_ = lean_st_ref_get(v___x_1138_);
lean_dec(v___x_1138_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed(lean_object* v_usedInstIdxs_1143_, lean_object* v___f_1144_, lean_object* v_e_1145_, lean_object* v___x_1146_, lean_object* v_x_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v___x_7557__boxed_1149_; lean_object* v_res_1150_; 
v___x_7557__boxed_1149_ = lean_unbox(v___x_1146_);
v_res_1150_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(v_usedInstIdxs_1143_, v___f_1144_, v_e_1145_, v___x_7557__boxed_1149_, v_x_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(lean_object* v_usedInstIdxs_1151_, lean_object* v_localInst2Index_1152_, lean_object* v_e_1153_){
_start:
{
if (lean_obj_tag(v_localInst2Index_1152_) == 0)
{
lean_object* v___f_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; lean_object* v_snd_1159_; 
v___f_1154_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1154_, 0, v_localInst2Index_1152_);
v___x_1155_ = 0;
v___x_1156_ = lean_box(v___x_1155_);
v___f_1157_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1157_, 0, v_usedInstIdxs_1151_);
lean_closure_set(v___f_1157_, 1, v___f_1154_);
lean_closure_set(v___f_1157_, 2, v_e_1153_);
lean_closure_set(v___f_1157_, 3, v___x_1156_);
v___x_1158_ = l_runST___redArg(v___f_1157_);
v_snd_1159_ = lean_ctor_get(v___x_1158_, 1);
lean_inc(v_snd_1159_);
lean_dec(v___x_1158_);
return v_snd_1159_;
}
else
{
lean_dec_ref(v_e_1153_);
return v_usedInstIdxs_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(lean_object* v_00_u03b4_1160_, lean_object* v_t_1161_, lean_object* v_k_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_1161_, v_k_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___boxed(lean_object* v_00_u03b4_1164_, lean_object* v_t_1165_, lean_object* v_k_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(v_00_u03b4_1164_, v_t_1165_, v_k_1166_);
lean_dec(v_k_1166_);
lean_dec(v_t_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(lean_object* v_00_u03b2_1168_, lean_object* v_k_1169_, lean_object* v_t_1170_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_1169_, v_t_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___boxed(lean_object* v_00_u03b2_1172_, lean_object* v_k_1173_, lean_object* v_t_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(v_00_u03b2_1172_, v_k_1173_, v_t_1174_);
lean_dec(v_t_1174_);
lean_dec(v_k_1173_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2(lean_object* v_00_u03b2_1177_, lean_object* v_k_1178_, lean_object* v_v_1179_, lean_object* v_t_1180_, lean_object* v_hl_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_1178_, v_v_1179_, v_t_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(lean_object* v_x_1183_, lean_object* v_p_1184_, lean_object* v_f_1185_, lean_object* v_e_1186_, uint8_t v_stopWhenVisited_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1184_, v_f_1185_, v_e_1186_, v_stopWhenVisited_1187_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___boxed(lean_object* v_x_1191_, lean_object* v_p_1192_, lean_object* v_f_1193_, lean_object* v_e_1194_, lean_object* v_stopWhenVisited_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1198_; lean_object* v_res_1199_; 
v_stopWhenVisited_boxed_1198_ = lean_unbox(v_stopWhenVisited_1195_);
v_res_1199_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(v_x_1191_, v_p_1192_, v_f_1193_, v_e_1194_, v_stopWhenVisited_boxed_1198_, v___y_1196_);
lean_dec(v___y_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(lean_object* v_x_1200_, lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_1201_, v_a_1202_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___boxed(lean_object* v_x_1206_, lean_object* v_e_1207_, lean_object* v_a_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(v_x_1206_, v_e_1207_, v_a_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec(v_a_1208_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(lean_object* v_x_1213_, lean_object* v_p_1214_, lean_object* v_f_1215_, uint8_t v_stopWhenVisited_1216_, lean_object* v_e_1217_, lean_object* v_a_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1214_, v_f_1215_, v_stopWhenVisited_1216_, v_e_1217_, v_a_1218_, v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___boxed(lean_object* v_x_1222_, lean_object* v_p_1223_, lean_object* v_f_1224_, lean_object* v_stopWhenVisited_1225_, lean_object* v_e_1226_, lean_object* v_a_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1230_; lean_object* v_res_1231_; 
v_stopWhenVisited_boxed_1230_ = lean_unbox(v_stopWhenVisited_1225_);
v_res_1231_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(v_x_1222_, v_p_1223_, v_f_1224_, v_stopWhenVisited_boxed_1230_, v_e_1226_, v_a_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec(v_a_1227_);
return v_res_1231_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(lean_object* v_x_1232_, lean_object* v_e_1233_, lean_object* v_a_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_1233_, v_a_1234_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___boxed(lean_object* v_x_1238_, lean_object* v_e_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_res_1243_; lean_object* v_r_1244_; 
v_res_1243_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(v_x_1238_, v_e_1239_, v_a_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec(v_a_1240_);
v_r_1244_ = lean_box(v_res_1243_);
return v_r_1244_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1245_, lean_object* v_m_1246_, lean_object* v_a_1247_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_1246_, v_a_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1249_, lean_object* v_m_1250_, lean_object* v_a_1251_){
_start:
{
uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_res_1252_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(v_00_u03b2_1249_, v_m_1250_, v_a_1251_);
lean_dec_ref(v_a_1251_);
lean_dec_ref(v_m_1250_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1254_, lean_object* v_m_1255_, lean_object* v_query_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_m_1255_, v_query_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1258_, lean_object* v_m_1259_, lean_object* v_query_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(v_00_u03b2_1258_, v_m_1259_, v_query_1260_);
lean_dec_ref(v_query_1260_);
lean_dec_ref(v_m_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1262_, lean_object* v_m_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___redArg(v_m_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_m_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8(v_00_u03b2_1265_, v_m_1266_);
lean_dec_ref(v_m_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1268_, lean_object* v_m_1269_, lean_object* v_query_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_m_1269_, v_query_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1272_, lean_object* v_m_1273_, lean_object* v_query_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(v_00_u03b2_1272_, v_m_1273_, v_query_1274_);
lean_dec_ref(v_query_1274_);
lean_dec_ref(v_m_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_1276_, lean_object* v_m_1277_, lean_object* v_query_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_m_1277_, v_query_1278_, v_x_1279_, v_x_1280_, v_x_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b2_1284_, lean_object* v_m_1285_, lean_object* v_query_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(v_00_u03b2_1284_, v_m_1285_, v_query_1286_, v_x_1287_, v_x_1288_, v_x_1289_, v_x_1290_);
lean_dec_ref(v_query_1286_);
lean_dec_ref(v_m_1285_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1292_, lean_object* v_init_1293_, lean_object* v_b_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___redArg(v_init_1293_, v_b_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1296_, lean_object* v_init_1297_, lean_object* v_b_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_1296_, v_init_1297_, v_b_1298_);
lean_dec_ref(v_b_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1300_, lean_object* v_b_1301_, lean_object* v_acc_1302_, lean_object* v_i_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___redArg(v_b_1301_, v_acc_1302_, v_i_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12___boxed(lean_object* v_00_u03b2_1305_, lean_object* v_b_1306_, lean_object* v_acc_1307_, lean_object* v_i_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__8_spec__11_spec__12(v_00_u03b2_1305_, v_b_1306_, v_acc_1307_, v_i_1308_);
lean_dec_ref(v_b_1306_);
return v_res_1309_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10(void){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Array_mkArray0(lean_box(0));
return v___x_1326_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0));
v___x_1342_ = l_String_toRawSubstring_x27(v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(lean_object* v_upperBound_1355_, lean_object* v_usedInstIdxs_1356_, lean_object* v_a_1357_, lean_object* v_b_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_a_1363_; uint8_t v___x_1367_; 
v___x_1367_ = lean_nat_dec_lt(v_a_1357_, v_upperBound_1355_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_dec(v_a_1357_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_b_1358_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1));
v___x_1370_ = l_Lean_Core_mkFreshUserName(v___x_1369_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v_fst_1372_; lean_object* v_snd_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1416_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v_fst_1372_ = lean_ctor_get(v_b_1358_, 0);
v_snd_1373_ = lean_ctor_get(v_b_1358_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_b_1358_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1375_ = v_b_1358_;
v_isShared_1376_ = v_isSharedCheck_1416_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_snd_1373_);
lean_inc(v_fst_1372_);
lean_dec(v_b_1358_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1416_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_ref_1377_; lean_object* v_quotContext_1378_; lean_object* v_currMacroScope_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_ref_1377_ = lean_ctor_get(v___y_1359_, 5);
v_quotContext_1378_ = lean_ctor_get(v___y_1359_, 10);
v_currMacroScope_1379_ = lean_ctor_get(v___y_1359_, 11);
v___x_1380_ = l_Lean_mkIdent(v_a_1371_);
lean_inc(v___x_1380_);
v___x_1381_ = lean_array_push(v_fst_1372_, v___x_1380_);
v___x_1382_ = 0;
v___x_1383_ = l_Lean_SourceInfo_fromRef(v_ref_1377_, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6));
v___x_1385_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_1383_, 5);
v___x_1386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1383_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1388_ = l_Lean_Syntax_node1(v___x_1383_, v___x_1387_, v___x_1380_);
v___x_1389_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1383_);
lean_ctor_set(v___x_1390_, 1, v___x_1387_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_1392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1383_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
lean_inc_ref(v___x_1390_);
lean_inc(v___x_1388_);
v___x_1393_ = l_Lean_Syntax_node4(v___x_1383_, v___x_1384_, v___x_1386_, v___x_1388_, v___x_1390_, v___x_1392_);
v___x_1394_ = lean_array_push(v_snd_1373_, v___x_1393_);
v___x_1395_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_a_1357_, v_usedInstIdxs_1356_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref_known(v___x_1390_, 3);
lean_dec(v___x_1388_);
lean_dec(v___x_1383_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1394_);
lean_ctor_set(v___x_1375_, 0, v___x_1381_);
v___x_1397_ = v___x_1375_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1394_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
v_a_1363_ = v___x_1397_;
goto v___jp_1362_;
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1399_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13));
v___x_1400_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14));
lean_inc_n(v___x_1383_, 4);
v___x_1401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1383_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1403_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1404_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1379_);
lean_inc(v_quotContext_1378_);
v___x_1405_ = l_Lean_addMacroScope(v_quotContext_1378_, v___x_1404_, v_currMacroScope_1379_);
v___x_1406_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1383_);
lean_ctor_set(v___x_1407_, 1, v___x_1403_);
lean_ctor_set(v___x_1407_, 2, v___x_1405_);
lean_ctor_set(v___x_1407_, 3, v___x_1406_);
v___x_1408_ = l_Lean_Syntax_node2(v___x_1383_, v___x_1402_, v___x_1407_, v___x_1388_);
v___x_1409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22));
v___x_1410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1383_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_Syntax_node4(v___x_1383_, v___x_1399_, v___x_1401_, v___x_1390_, v___x_1408_, v___x_1410_);
v___x_1412_ = lean_array_push(v___x_1394_, v___x_1411_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1412_);
lean_ctor_set(v___x_1375_, 0, v___x_1381_);
v___x_1414_ = v___x_1375_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
v_a_1363_ = v___x_1414_;
goto v___jp_1362_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_b_1358_);
lean_dec(v_a_1357_);
v_a_1417_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1370_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1370_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
v___jp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = lean_nat_add(v_a_1357_, v___x_1364_);
lean_dec(v_a_1357_);
v_a_1357_ = v___x_1365_;
v_b_1358_ = v_a_1363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___boxed(lean_object* v_upperBound_1425_, lean_object* v_usedInstIdxs_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1425_, v_usedInstIdxs_1426_, v_a_1427_, v_b_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_usedInstIdxs_1426_);
lean_dec(v_upperBound_1425_);
return v_res_1432_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_box(1);
v___x_1434_ = l_Lean_MessageData_ofFormat(v___x_1433_);
return v___x_1434_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2));
v___x_1439_ = l_Lean_MessageData_ofFormat(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
if (lean_obj_tag(v_x_1441_) == 0)
{
return v_x_1440_;
}
else
{
lean_object* v_head_1442_; lean_object* v_tail_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1465_; 
v_head_1442_ = lean_ctor_get(v_x_1441_, 0);
v_tail_1443_ = lean_ctor_get(v_x_1441_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1441_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1445_ = v_x_1441_;
v_isShared_1446_ = v_isSharedCheck_1465_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_tail_1443_);
lean_inc(v_head_1442_);
lean_dec(v_x_1441_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1465_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v_before_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1463_; 
v_before_1447_ = lean_ctor_get(v_head_1442_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_head_1442_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_head_1442_, 1);
lean_dec(v_unused_1464_);
v___x_1449_ = v_head_1442_;
v_isShared_1450_ = v_isSharedCheck_1463_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_before_1447_);
lean_dec(v_head_1442_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1463_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 7);
lean_ctor_set(v___x_1449_, 1, v___x_1451_);
lean_ctor_set(v___x_1449_, 0, v_x_1440_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_x_1440_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 7);
lean_ctor_set(v___x_1445_, 1, v___x_1454_);
lean_ctor_set(v___x_1445_, 0, v___x_1453_);
v___x_1456_ = v___x_1445_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = l_Lean_MessageData_ofSyntax(v_before_1447_);
v___x_1458_ = l_Lean_indentD(v___x_1457_);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1456_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v_x_1440_ = v___x_1459_;
v_x_1441_ = v_tail_1443_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_1466_, lean_object* v_opt_1467_){
_start:
{
lean_object* v_name_1468_; lean_object* v_defValue_1469_; lean_object* v_map_1470_; lean_object* v___x_1471_; 
v_name_1468_ = lean_ctor_get(v_opt_1467_, 0);
v_defValue_1469_ = lean_ctor_get(v_opt_1467_, 1);
v_map_1470_ = lean_ctor_get(v_opts_1466_, 0);
v___x_1471_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1470_, v_name_1468_);
if (lean_obj_tag(v___x_1471_) == 0)
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_unbox(v_defValue_1469_);
return v___x_1472_;
}
else
{
lean_object* v_val_1473_; 
v_val_1473_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v___x_1471_, 1);
if (lean_obj_tag(v_val_1473_) == 1)
{
uint8_t v_v_1474_; 
v_v_1474_ = lean_ctor_get_uint8(v_val_1473_, 0);
lean_dec_ref_known(v_val_1473_, 0);
return v_v_1474_;
}
else
{
uint8_t v___x_1475_; 
lean_dec(v_val_1473_);
v___x_1475_ = lean_unbox(v_defValue_1469_);
return v___x_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_1476_, lean_object* v_opt_1477_){
_start:
{
uint8_t v_res_1478_; lean_object* v_r_1479_; 
v_res_1478_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_1476_, v_opt_1477_);
lean_dec_ref(v_opt_1477_);
lean_dec_ref(v_opts_1476_);
v_r_1479_ = lean_box(v_res_1478_);
return v_r_1479_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1484_ = l_Lean_MessageData_ofFormat(v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_1485_, lean_object* v_macroStack_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_options_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v_options_1489_ = lean_ctor_get(v___y_1487_, 2);
v___x_1490_ = l_Lean_Elab_pp_macroStack;
v___x_1491_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
lean_dec(v_macroStack_1486_);
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_msgData_1485_);
return v___x_1492_;
}
else
{
if (lean_obj_tag(v_macroStack_1486_) == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_msgData_1485_);
return v___x_1493_;
}
else
{
lean_object* v_head_1494_; lean_object* v_after_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1510_; 
v_head_1494_ = lean_ctor_get(v_macroStack_1486_, 0);
lean_inc(v_head_1494_);
v_after_1495_ = lean_ctor_get(v_head_1494_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_head_1494_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_head_1494_, 0);
lean_dec(v_unused_1511_);
v___x_1497_ = v_head_1494_;
v_isShared_1498_ = v_isSharedCheck_1510_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_after_1495_);
lean_dec(v_head_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1510_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 7);
lean_ctor_set(v___x_1497_, 1, v___x_1499_);
lean_ctor_set(v___x_1497_, 0, v_msgData_1485_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_msgData_1485_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_msgData_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1502_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = l_Lean_MessageData_ofSyntax(v_after_1495_);
v___x_1505_ = l_Lean_indentD(v___x_1504_);
v_msgData_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1506_, 0, v___x_1503_);
lean_ctor_set(v_msgData_1506_, 1, v___x_1505_);
v___x_1507_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_1506_, v_macroStack_1486_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1512_, lean_object* v_macroStack_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1512_, v_macroStack_1513_, v___y_1514_);
lean_dec_ref(v___y_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(lean_object* v_msg_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_ref_1525_; lean_object* v___x_1526_; lean_object* v_a_1527_; lean_object* v_macroStack_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1539_; 
v_ref_1525_ = lean_ctor_get(v___y_1522_, 5);
v___x_1526_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1517_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
v_macroStack_1528_ = lean_ctor_get(v___y_1518_, 1);
v___x_1529_ = l_Lean_Elab_getBetterRef(v_ref_1525_, v_macroStack_1528_);
lean_inc(v_macroStack_1528_);
v___x_1530_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_a_1527_, v_macroStack_1528_, v___y_1522_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1529_);
lean_ctor_set(v___x_1535_, 1, v_a_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set_tag(v___x_1533_, 1);
lean_ctor_set(v___x_1533_, 0, v___x_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1548_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(lean_object* v_constName_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v_env_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_st_ref_get(v___y_1561_);
v_env_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_env_1564_);
lean_dec(v___x_1563_);
lean_inc(v_constName_1555_);
v___x_1565_ = l_Lean_isInductiveCore_x3f(v_env_1564_, v_constName_1555_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1566_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_1567_ = 0;
v___x_1568_ = l_Lean_MessageData_ofConstName(v_constName_1555_, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1566_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_1571_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v___x_1572_;
}
else
{
lean_object* v_val_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_constName_1555_);
v_val_1573_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1565_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_val_1573_);
lean_dec(v___x_1565_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 0);
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_val_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___boxed(lean_object* v_constName_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_constName_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(size_t v_sz_1590_, size_t v_i_1591_, lean_object* v_bs_1592_){
_start:
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_usize_dec_lt(v_i_1591_, v_sz_1590_);
if (v___x_1593_ == 0)
{
return v_bs_1592_;
}
else
{
lean_object* v_v_1594_; lean_object* v___x_1595_; lean_object* v_bs_x27_1596_; size_t v___x_1597_; size_t v___x_1598_; lean_object* v___x_1599_; 
v_v_1594_ = lean_array_uget(v_bs_1592_, v_i_1591_);
v___x_1595_ = lean_unsigned_to_nat(0u);
v_bs_x27_1596_ = lean_array_uset(v_bs_1592_, v_i_1591_, v___x_1595_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_add(v_i_1591_, v___x_1597_);
v___x_1599_ = lean_array_uset(v_bs_x27_1596_, v_i_1591_, v_v_1594_);
v_i_1591_ = v___x_1598_;
v_bs_1592_ = v___x_1599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0___boxed(lean_object* v_sz_1601_, lean_object* v_i_1602_, lean_object* v_bs_1603_){
_start:
{
size_t v_sz_boxed_1604_; size_t v_i_boxed_1605_; lean_object* v_res_1606_; 
v_sz_boxed_1604_ = lean_unbox_usize(v_sz_1601_);
lean_dec(v_sz_1601_);
v_i_boxed_1605_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v_res_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_boxed_1604_, v_i_boxed_1605_, v_bs_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(lean_object* v_inductiveTypeName_1684_, lean_object* v_instId_1685_, lean_object* v_usedInstIdxs_1686_, lean_object* v_auxFunId_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
lean_inc(v_inductiveTypeName_1684_);
v___x_1695_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_1684_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_numParams_1697_; lean_object* v_numIndices_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v_numParams_1697_ = lean_ctor_get(v_a_1696_, 1);
lean_inc(v_numParams_1697_);
v_numIndices_1698_ = lean_ctor_get(v_a_1696_, 2);
lean_inc(v_numIndices_1698_);
lean_dec(v_a_1696_);
v___x_1699_ = lean_unsigned_to_nat(0u);
v___x_1700_ = lean_nat_add(v_numParams_1697_, v_numIndices_1698_);
lean_dec(v_numIndices_1698_);
lean_dec(v_numParams_1697_);
v___x_1701_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1));
v___x_1702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v___x_1700_, v_usedInstIdxs_1686_, v___x_1699_, v___x_1701_, v_a_1692_, v_a_1693_);
lean_dec(v___x_1700_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1779_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1779_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1779_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_fst_1707_; lean_object* v_snd_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1778_; 
v_fst_1707_ = lean_ctor_get(v_a_1703_, 0);
v_snd_1708_ = lean_ctor_get(v_a_1703_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_a_1703_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1710_ = v_a_1703_;
v_isShared_1711_ = v_isSharedCheck_1778_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_snd_1708_);
lean_inc(v_fst_1707_);
lean_dec(v_a_1703_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1778_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_ref_1712_; lean_object* v_quotContext_1713_; lean_object* v_currMacroScope_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v_ref_1712_ = lean_ctor_get(v_a_1692_, 5);
v_quotContext_1713_ = lean_ctor_get(v_a_1692_, 10);
v_currMacroScope_1714_ = lean_ctor_get(v_a_1692_, 11);
v___x_1715_ = 0;
v___x_1716_ = l_Lean_SourceInfo_fromRef(v_ref_1712_, v___x_1715_);
v___x_1717_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1718_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3));
v___x_1719_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4));
lean_inc(v___x_1716_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 2);
lean_ctor_set(v___x_1710_, 1, v___x_1719_);
lean_ctor_set(v___x_1710_, 0, v___x_1716_);
v___x_1721_ = v___x_1710_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; size_t v_sz_1742_; size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1722_ = l_Lean_mkCIdent(v_inductiveTypeName_1684_);
lean_inc_n(v___x_1716_, 24);
v___x_1723_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1718_, v___x_1721_, v___x_1722_);
v___x_1724_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1725_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1726_ = l_Array_append___redArg(v___x_1725_, v_fst_1707_);
lean_dec(v_fst_1707_);
v___x_1727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1716_);
lean_ctor_set(v___x_1727_, 1, v___x_1724_);
lean_ctor_set(v___x_1727_, 2, v___x_1726_);
v___x_1728_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1717_, v___x_1723_, v___x_1727_);
v___x_1729_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7));
v___x_1730_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9));
v___x_1731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1716_);
lean_ctor_set(v___x_1731_, 1, v___x_1724_);
lean_ctor_set(v___x_1731_, 2, v___x_1725_);
lean_inc_ref_n(v___x_1731_, 12);
v___x_1732_ = l_Lean_Syntax_node7(v___x_1716_, v___x_1730_, v___x_1731_, v___x_1731_, v___x_1731_, v___x_1731_, v___x_1731_, v___x_1731_, v___x_1731_);
v___x_1733_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10));
v___x_1734_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11));
v___x_1735_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13));
v___x_1736_ = l_Lean_Syntax_node1(v___x_1716_, v___x_1735_, v___x_1731_);
v___x_1737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1716_);
lean_ctor_set(v___x_1737_, 1, v___x_1733_);
v___x_1738_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15));
v___x_1739_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1738_, v_instId_1685_, v___x_1731_);
v___x_1740_ = l_Lean_Syntax_node1(v___x_1716_, v___x_1724_, v___x_1739_);
v___x_1741_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17));
v_sz_1742_ = lean_array_size(v_snd_1708_);
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_1742_, v___x_1743_, v_snd_1708_);
v___x_1745_ = l_Array_append___redArg(v___x_1725_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1716_);
lean_ctor_set(v___x_1746_, 1, v___x_1724_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
v___x_1747_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19));
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20));
v___x_1749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1716_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1751_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1714_);
lean_inc(v_quotContext_1713_);
v___x_1752_ = l_Lean_addMacroScope(v_quotContext_1713_, v___x_1751_, v_currMacroScope_1714_);
v___x_1753_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1754_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1716_);
lean_ctor_set(v___x_1754_, 1, v___x_1750_);
lean_ctor_set(v___x_1754_, 2, v___x_1752_);
lean_ctor_set(v___x_1754_, 3, v___x_1753_);
v___x_1755_ = l_Lean_Syntax_node1(v___x_1716_, v___x_1724_, v___x_1728_);
v___x_1756_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1717_, v___x_1754_, v___x_1755_);
v___x_1757_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1747_, v___x_1749_, v___x_1756_);
v___x_1758_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1741_, v___x_1746_, v___x_1757_);
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22));
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23));
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1716_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25));
v___x_1763_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26));
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1716_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_Syntax_node1(v___x_1716_, v___x_1724_, v_auxFunId_1687_);
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27));
v___x_1767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1716_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_Syntax_node3(v___x_1716_, v___x_1762_, v___x_1764_, v___x_1765_, v___x_1767_);
v___x_1769_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30));
v___x_1770_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1769_, v___x_1731_, v___x_1731_);
v___x_1771_ = l_Lean_Syntax_node4(v___x_1716_, v___x_1759_, v___x_1761_, v___x_1768_, v___x_1770_, v___x_1731_);
v___x_1772_ = l_Lean_Syntax_node6(v___x_1716_, v___x_1734_, v___x_1736_, v___x_1737_, v___x_1731_, v___x_1740_, v___x_1758_, v___x_1771_);
v___x_1773_ = l_Lean_Syntax_node2(v___x_1716_, v___x_1729_, v___x_1732_, v___x_1772_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1773_);
v___x_1775_ = v___x_1705_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_auxFunId_1687_);
lean_dec(v_instId_1685_);
lean_dec(v_inductiveTypeName_1684_);
v_a_1780_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1702_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1702_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_auxFunId_1687_);
lean_dec(v_instId_1685_);
lean_dec(v_inductiveTypeName_1684_);
v_a_1788_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1695_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1695_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___boxed(lean_object* v_inductiveTypeName_1796_, lean_object* v_instId_1797_, lean_object* v_usedInstIdxs_1798_, lean_object* v_auxFunId_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_1796_, v_instId_1797_, v_usedInstIdxs_1798_, v_auxFunId_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_usedInstIdxs_1798_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(lean_object* v_upperBound_1808_, lean_object* v_usedInstIdxs_1809_, lean_object* v_inst_1810_, lean_object* v_R_1811_, lean_object* v_a_1812_, lean_object* v_b_1813_, lean_object* v_c_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1808_, v_usedInstIdxs_1809_, v_a_1812_, v_b_1813_, v___y_1819_, v___y_1820_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___boxed(lean_object* v_upperBound_1823_, lean_object* v_usedInstIdxs_1824_, lean_object* v_inst_1825_, lean_object* v_R_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_, lean_object* v_c_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(v_upperBound_1823_, v_usedInstIdxs_1824_, v_inst_1825_, v_R_1826_, v_a_1827_, v_b_1828_, v_c_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v_usedInstIdxs_1824_);
lean_dec(v_upperBound_1823_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_object* v_00_u03b1_1838_, lean_object* v_msg_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_msg_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(v_00_u03b1_1848_, v_msg_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(lean_object* v_msgData_1858_, lean_object* v_macroStack_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1858_, v_macroStack_1859_, v___y_1864_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1868_, lean_object* v_macroStack_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(v_msgData_1868_, v_macroStack_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1877_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = lean_unsigned_to_nat(32u);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1881_ = ((size_t)5ULL);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_unsigned_to_nat(32u);
v___x_1884_ = lean_mk_empty_array_with_capacity(v___x_1883_);
v___x_1885_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0);
v___x_1886_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___x_1884_);
lean_ctor_set(v___x_1886_, 2, v___x_1882_);
lean_ctor_set(v___x_1886_, 3, v___x_1882_);
lean_ctor_set_usize(v___x_1886_, 4, v___x_1881_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v_traceState_1890_; lean_object* v_traces_1891_; lean_object* v___x_1892_; lean_object* v_traceState_1893_; lean_object* v_env_1894_; lean_object* v_nextMacroScope_1895_; lean_object* v_ngen_1896_; lean_object* v_auxDeclNGen_1897_; lean_object* v_cache_1898_; lean_object* v_messages_1899_; lean_object* v_infoState_1900_; lean_object* v_snapshotTasks_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1920_; 
v___x_1889_ = lean_st_ref_get(v___y_1887_);
v_traceState_1890_ = lean_ctor_get(v___x_1889_, 4);
lean_inc_ref(v_traceState_1890_);
lean_dec(v___x_1889_);
v_traces_1891_ = lean_ctor_get(v_traceState_1890_, 0);
lean_inc_ref(v_traces_1891_);
lean_dec_ref(v_traceState_1890_);
v___x_1892_ = lean_st_ref_take(v___y_1887_);
v_traceState_1893_ = lean_ctor_get(v___x_1892_, 4);
v_env_1894_ = lean_ctor_get(v___x_1892_, 0);
v_nextMacroScope_1895_ = lean_ctor_get(v___x_1892_, 1);
v_ngen_1896_ = lean_ctor_get(v___x_1892_, 2);
v_auxDeclNGen_1897_ = lean_ctor_get(v___x_1892_, 3);
v_cache_1898_ = lean_ctor_get(v___x_1892_, 5);
v_messages_1899_ = lean_ctor_get(v___x_1892_, 6);
v_infoState_1900_ = lean_ctor_get(v___x_1892_, 7);
v_snapshotTasks_1901_ = lean_ctor_get(v___x_1892_, 8);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1903_ = v___x_1892_;
v_isShared_1904_ = v_isSharedCheck_1920_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snapshotTasks_1901_);
lean_inc(v_infoState_1900_);
lean_inc(v_messages_1899_);
lean_inc(v_cache_1898_);
lean_inc(v_traceState_1893_);
lean_inc(v_auxDeclNGen_1897_);
lean_inc(v_ngen_1896_);
lean_inc(v_nextMacroScope_1895_);
lean_inc(v_env_1894_);
lean_dec(v___x_1892_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1920_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
uint64_t v_tid_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1918_; 
v_tid_1905_ = lean_ctor_get_uint64(v_traceState_1893_, sizeof(void*)*1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_traceState_1893_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v_traceState_1893_, 0);
lean_dec(v_unused_1919_);
v___x_1907_ = v_traceState_1893_;
v_isShared_1908_ = v_isSharedCheck_1918_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v_traceState_1893_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1918_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1909_);
lean_ctor_set_uint64(v_reuseFailAlloc_1917_, sizeof(void*)*1, v_tid_1905_);
v___x_1911_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 4, v___x_1911_);
v___x_1913_ = v___x_1903_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_env_1894_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_nextMacroScope_1895_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_ngen_1896_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_auxDeclNGen_1897_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1916_, 5, v_cache_1898_);
lean_ctor_set(v_reuseFailAlloc_1916_, 6, v_messages_1899_);
lean_ctor_set(v_reuseFailAlloc_1916_, 7, v_infoState_1900_);
lean_ctor_set(v_reuseFailAlloc_1916_, 8, v_snapshotTasks_1901_);
v___x_1913_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_st_ref_put(v___y_1887_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_traces_1891_);
return v___x_1915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___boxed(lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1921_);
lean_dec(v___y_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object* v_x_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
v___x_1948_ = lean_apply_7(v_x_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, lean_box(0));
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(v_x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object* v_mvarId_1958_, lean_object* v_x_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___f_1967_; lean_object* v___x_1968_; 
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
v___f_1967_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1967_, 0, v_x_1959_);
lean_closure_set(v___f_1967_, 1, v___y_1960_);
lean_closure_set(v___f_1967_, 2, v___y_1961_);
v___x_1968_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1958_, v___f_1967_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
return v___x_1968_;
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object* v_mvarId_1977_, lean_object* v_x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1977_, v_x_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object* v_00_u03b1_1987_, lean_object* v_mvarId_1988_, lean_object* v_x_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1988_, v_x_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_mvarId_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(v_00_u03b1_1998_, v_mvarId_1999_, v_x_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2008_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0));
v___x_2011_ = l_Lean_stringToMessageData(v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object* v_a_2012_, lean_object* v_x_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2021_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1);
v___x_2022_ = lean_unsigned_to_nat(30u);
v___x_2023_ = l_Lean_inlineExprTrailing(v_a_2012_, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2021_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object* v_a_2026_, lean_object* v_x_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(v_a_2026_, v_x_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_x_2027_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object* v_x_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_ks_2040_; lean_object* v_vs_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2065_; 
v_ks_2040_ = lean_ctor_get(v_x_2036_, 0);
v_vs_2041_ = lean_ctor_get(v_x_2036_, 1);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_x_2036_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2043_ = v_x_2036_;
v_isShared_2044_ = v_isSharedCheck_2065_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_vs_2041_);
lean_inc(v_ks_2040_);
lean_dec(v_x_2036_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2065_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = lean_array_get_size(v_ks_2040_);
v___x_2046_ = lean_nat_dec_lt(v_x_2037_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
lean_dec(v_x_2037_);
v___x_2047_ = lean_array_push(v_ks_2040_, v_x_2038_);
v___x_2048_ = lean_array_push(v_vs_2041_, v_x_2039_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___x_2048_);
lean_ctor_set(v___x_2043_, 0, v___x_2047_);
v___x_2050_ = v___x_2043_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
else
{
lean_object* v_k_x27_2052_; uint8_t v___x_2053_; 
v_k_x27_2052_ = lean_array_fget_borrowed(v_ks_2040_, v_x_2037_);
v___x_2053_ = l_Lean_instBEqMVarId_beq(v_x_2038_, v_k_x27_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2055_; 
if (v_isShared_2044_ == 0)
{
v___x_2055_ = v___x_2043_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_ks_2040_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_vs_2041_);
v___x_2055_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_add(v_x_2037_, v___x_2056_);
lean_dec(v_x_2037_);
v_x_2036_ = v___x_2055_;
v_x_2037_ = v___x_2057_;
goto _start;
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2060_ = lean_array_fset(v_ks_2040_, v_x_2037_, v_x_2038_);
v___x_2061_ = lean_array_fset(v_vs_2041_, v_x_2037_, v_x_2039_);
lean_dec(v_x_2037_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___x_2061_);
lean_ctor_set(v___x_2043_, 0, v___x_2060_);
v___x_2063_ = v___x_2043_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_n_2066_, lean_object* v_k_2067_, lean_object* v_v_2068_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_n_2066_, v___x_2069_, v_k_2067_, v_v_2068_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2072_, size_t v_x_2073_, size_t v_x_2074_, lean_object* v_x_2075_, lean_object* v_x_2076_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
lean_object* v_es_2077_; size_t v___x_2078_; size_t v___x_2079_; lean_object* v_j_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_es_2077_ = lean_ctor_get(v_x_2072_, 0);
v___x_2078_ = ((size_t)31ULL);
v___x_2079_ = lean_usize_land(v_x_2073_, v___x_2078_);
v_j_2080_ = lean_usize_to_nat(v___x_2079_);
v___x_2081_ = lean_array_get_size(v_es_2077_);
v___x_2082_ = lean_nat_dec_lt(v_j_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec(v_j_2080_);
lean_dec(v_x_2076_);
lean_dec(v_x_2075_);
return v_x_2072_;
}
else
{
lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2121_; 
lean_inc_ref(v_es_2077_);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_x_2072_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v_x_2072_, 0);
lean_dec(v_unused_2122_);
v___x_2084_ = v_x_2072_;
v_isShared_2085_ = v_isSharedCheck_2121_;
goto v_resetjp_2083_;
}
else
{
lean_dec(v_x_2072_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2121_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_v_2086_; lean_object* v___x_2087_; lean_object* v_xs_x27_2088_; lean_object* v___y_2090_; 
v_v_2086_ = lean_array_fget(v_es_2077_, v_j_2080_);
v___x_2087_ = lean_box(0);
v_xs_x27_2088_ = lean_array_fset(v_es_2077_, v_j_2080_, v___x_2087_);
switch(lean_obj_tag(v_v_2086_))
{
case 0:
{
lean_object* v_key_2095_; lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2106_; 
v_key_2095_ = lean_ctor_get(v_v_2086_, 0);
v_val_2096_ = lean_ctor_get(v_v_2086_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_v_2086_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2098_ = v_v_2086_;
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_inc(v_key_2095_);
lean_dec(v_v_2086_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
uint8_t v___x_2100_; 
v___x_2100_ = l_Lean_instBEqMVarId_beq(v_x_2075_, v_key_2095_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_del_object(v___x_2098_);
v___x_2101_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2095_, v_val_2096_, v_x_2075_, v_x_2076_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___y_2090_ = v___x_2102_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2104_; 
lean_dec(v_val_2096_);
lean_dec(v_key_2095_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v_x_2076_);
lean_ctor_set(v___x_2098_, 0, v_x_2075_);
v___x_2104_ = v___x_2098_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_x_2075_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_x_2076_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v___y_2090_ = v___x_2104_;
goto v___jp_2089_;
}
}
}
}
case 1:
{
lean_object* v_node_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2119_; 
v_node_2107_ = lean_ctor_get(v_v_2086_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_v_2086_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2109_ = v_v_2086_;
v_isShared_2110_ = v_isSharedCheck_2119_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_node_2107_);
lean_dec(v_v_2086_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2119_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2111_ = ((size_t)5ULL);
v___x_2112_ = lean_usize_shift_right(v_x_2073_, v___x_2111_);
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_add(v_x_2074_, v___x_2113_);
v___x_2115_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_node_2107_, v___x_2112_, v___x_2114_, v_x_2075_, v_x_2076_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2115_);
v___x_2117_ = v___x_2109_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
v___y_2090_ = v___x_2117_;
goto v___jp_2089_;
}
}
}
default: 
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_x_2075_);
lean_ctor_set(v___x_2120_, 1, v_x_2076_);
v___y_2090_ = v___x_2120_;
goto v___jp_2089_;
}
}
v___jp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_array_fset(v_xs_x27_2088_, v_j_2080_, v___y_2090_);
lean_dec(v_j_2080_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2091_);
v___x_2093_ = v___x_2084_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
else
{
lean_object* v_ks_2123_; lean_object* v_vs_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2144_; 
v_ks_2123_ = lean_ctor_get(v_x_2072_, 0);
v_vs_2124_ = lean_ctor_get(v_x_2072_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_x_2072_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2126_ = v_x_2072_;
v_isShared_2127_ = v_isSharedCheck_2144_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_vs_2124_);
lean_inc(v_ks_2123_);
lean_dec(v_x_2072_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2144_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_ks_2123_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_vs_2124_);
v___x_2129_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v_newNode_2130_; uint8_t v___y_2132_; size_t v___x_2138_; uint8_t v___x_2139_; 
v_newNode_2130_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v___x_2129_, v_x_2075_, v_x_2076_);
v___x_2138_ = ((size_t)7ULL);
v___x_2139_ = lean_usize_dec_le(v___x_2138_, v_x_2074_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2130_);
v___x_2141_ = lean_unsigned_to_nat(4u);
v___x_2142_ = lean_nat_dec_lt(v___x_2140_, v___x_2141_);
lean_dec(v___x_2140_);
v___y_2132_ = v___x_2142_;
goto v___jp_2131_;
}
else
{
v___y_2132_ = v___x_2139_;
goto v___jp_2131_;
}
v___jp_2131_:
{
if (v___y_2132_ == 0)
{
lean_object* v_ks_2133_; lean_object* v_vs_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_ks_2133_ = lean_ctor_get(v_newNode_2130_, 0);
lean_inc_ref(v_ks_2133_);
v_vs_2134_ = lean_ctor_get(v_newNode_2130_, 1);
lean_inc_ref(v_vs_2134_);
lean_dec_ref(v_newNode_2130_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_2137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_x_2074_, v_ks_2133_, v_vs_2134_, v___x_2135_, v___x_2136_);
lean_dec_ref(v_vs_2134_);
lean_dec_ref(v_ks_2133_);
return v___x_2137_;
}
else
{
return v_newNode_2130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t v_depth_2145_, lean_object* v_keys_2146_, lean_object* v_vals_2147_, lean_object* v_i_2148_, lean_object* v_entries_2149_){
_start:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_array_get_size(v_keys_2146_);
v___x_2151_ = lean_nat_dec_lt(v_i_2148_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec(v_i_2148_);
return v_entries_2149_;
}
else
{
lean_object* v_k_2152_; lean_object* v_v_2153_; uint64_t v___x_2154_; size_t v_h_2155_; size_t v___x_2156_; lean_object* v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; size_t v_h_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_k_2152_ = lean_array_fget_borrowed(v_keys_2146_, v_i_2148_);
v_v_2153_ = lean_array_fget_borrowed(v_vals_2147_, v_i_2148_);
v___x_2154_ = l_Lean_instHashableMVarId_hash(v_k_2152_);
v_h_2155_ = lean_uint64_to_usize(v___x_2154_);
v___x_2156_ = ((size_t)5ULL);
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = ((size_t)1ULL);
v___x_2159_ = lean_usize_sub(v_depth_2145_, v___x_2158_);
v___x_2160_ = lean_usize_mul(v___x_2156_, v___x_2159_);
v_h_2161_ = lean_usize_shift_right(v_h_2155_, v___x_2160_);
v___x_2162_ = lean_nat_add(v_i_2148_, v___x_2157_);
lean_dec(v_i_2148_);
lean_inc(v_v_2153_);
lean_inc(v_k_2152_);
v___x_2163_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_entries_2149_, v_h_2161_, v_depth_2145_, v_k_2152_, v_v_2153_);
v_i_2148_ = v___x_2162_;
v_entries_2149_ = v___x_2163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_depth_2165_, lean_object* v_keys_2166_, lean_object* v_vals_2167_, lean_object* v_i_2168_, lean_object* v_entries_2169_){
_start:
{
size_t v_depth_boxed_2170_; lean_object* v_res_2171_; 
v_depth_boxed_2170_ = lean_unbox_usize(v_depth_2165_);
lean_dec(v_depth_2165_);
v_res_2171_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_boxed_2170_, v_keys_2166_, v_vals_2167_, v_i_2168_, v_entries_2169_);
lean_dec_ref(v_vals_2167_);
lean_dec_ref(v_keys_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
size_t v_x_18536__boxed_2177_; size_t v_x_18537__boxed_2178_; lean_object* v_res_2179_; 
v_x_18536__boxed_2177_ = lean_unbox_usize(v_x_2173_);
lean_dec(v_x_2173_);
v_x_18537__boxed_2178_ = lean_unbox_usize(v_x_2174_);
lean_dec(v_x_2174_);
v_res_2179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2172_, v_x_18536__boxed_2177_, v_x_18537__boxed_2178_, v_x_2175_, v_x_2176_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object* v_x_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
uint64_t v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2183_ = l_Lean_instHashableMVarId_hash(v_x_2181_);
v___x_2184_ = lean_uint64_to_usize(v___x_2183_);
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2180_, v___x_2184_, v___x_2185_, v_x_2181_, v_x_2182_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v_mvarId_2187_, lean_object* v_val_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; lean_object* v_mctx_2192_; lean_object* v_cache_2193_; lean_object* v_zetaDeltaFVarIds_2194_; lean_object* v_postponed_2195_; lean_object* v_diag_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2225_; 
v___x_2191_ = lean_st_ref_take(v___y_2189_);
v_mctx_2192_ = lean_ctor_get(v___x_2191_, 0);
v_cache_2193_ = lean_ctor_get(v___x_2191_, 1);
v_zetaDeltaFVarIds_2194_ = lean_ctor_get(v___x_2191_, 2);
v_postponed_2195_ = lean_ctor_get(v___x_2191_, 3);
v_diag_2196_ = lean_ctor_get(v___x_2191_, 4);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2198_ = v___x_2191_;
v_isShared_2199_ = v_isSharedCheck_2225_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_diag_2196_);
lean_inc(v_postponed_2195_);
lean_inc(v_zetaDeltaFVarIds_2194_);
lean_inc(v_cache_2193_);
lean_inc(v_mctx_2192_);
lean_dec(v___x_2191_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2225_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v_depth_2200_; lean_object* v_levelAssignDepth_2201_; lean_object* v_lmvarCounter_2202_; lean_object* v_mvarCounter_2203_; lean_object* v_lDecls_2204_; lean_object* v_decls_2205_; lean_object* v_userNames_2206_; lean_object* v_lAssignment_2207_; lean_object* v_eAssignment_2208_; lean_object* v_dAssignment_2209_; lean_object* v_instanceTypedMVars_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2224_; 
v_depth_2200_ = lean_ctor_get(v_mctx_2192_, 0);
v_levelAssignDepth_2201_ = lean_ctor_get(v_mctx_2192_, 1);
v_lmvarCounter_2202_ = lean_ctor_get(v_mctx_2192_, 2);
v_mvarCounter_2203_ = lean_ctor_get(v_mctx_2192_, 3);
v_lDecls_2204_ = lean_ctor_get(v_mctx_2192_, 4);
v_decls_2205_ = lean_ctor_get(v_mctx_2192_, 5);
v_userNames_2206_ = lean_ctor_get(v_mctx_2192_, 6);
v_lAssignment_2207_ = lean_ctor_get(v_mctx_2192_, 7);
v_eAssignment_2208_ = lean_ctor_get(v_mctx_2192_, 8);
v_dAssignment_2209_ = lean_ctor_get(v_mctx_2192_, 9);
v_instanceTypedMVars_2210_ = lean_ctor_get(v_mctx_2192_, 10);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_mctx_2192_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2212_ = v_mctx_2192_;
v_isShared_2213_ = v_isSharedCheck_2224_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_instanceTypedMVars_2210_);
lean_inc(v_dAssignment_2209_);
lean_inc(v_eAssignment_2208_);
lean_inc(v_lAssignment_2207_);
lean_inc(v_userNames_2206_);
lean_inc(v_decls_2205_);
lean_inc(v_lDecls_2204_);
lean_inc(v_mvarCounter_2203_);
lean_inc(v_lmvarCounter_2202_);
lean_inc(v_levelAssignDepth_2201_);
lean_inc(v_depth_2200_);
lean_dec(v_mctx_2192_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2224_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_eAssignment_2208_, v_mvarId_2187_, v_val_2188_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 8, v___x_2214_);
v___x_2216_ = v___x_2212_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_depth_2200_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_levelAssignDepth_2201_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_lmvarCounter_2202_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_mvarCounter_2203_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_lDecls_2204_);
lean_ctor_set(v_reuseFailAlloc_2223_, 5, v_decls_2205_);
lean_ctor_set(v_reuseFailAlloc_2223_, 6, v_userNames_2206_);
lean_ctor_set(v_reuseFailAlloc_2223_, 7, v_lAssignment_2207_);
lean_ctor_set(v_reuseFailAlloc_2223_, 8, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2223_, 9, v_dAssignment_2209_);
lean_ctor_set(v_reuseFailAlloc_2223_, 10, v_instanceTypedMVars_2210_);
v___x_2216_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2218_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2216_);
v___x_2218_ = v___x_2198_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_cache_2193_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_zetaDeltaFVarIds_2194_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_postponed_2195_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_diag_2196_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_st_ref_put(v___y_2189_, v___x_2218_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object* v_mvarId_2226_, lean_object* v_val_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2226_, v_val_2227_, v___y_2228_);
lean_dec(v___y_2228_);
return v_res_2230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(lean_object* v_e_2231_){
_start:
{
if (lean_obj_tag(v_e_2231_) == 0)
{
uint8_t v___x_2232_; 
v___x_2232_ = 2;
return v___x_2232_;
}
else
{
uint8_t v___x_2233_; 
v___x_2233_ = 0;
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___boxed(lean_object* v_e_2234_){
_start:
{
uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_res_2235_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_e_2234_);
lean_dec_ref(v_e_2234_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object* v_opts_2237_, lean_object* v_opt_2238_){
_start:
{
lean_object* v_name_2239_; lean_object* v_defValue_2240_; lean_object* v_map_2241_; lean_object* v___x_2242_; 
v_name_2239_ = lean_ctor_get(v_opt_2238_, 0);
v_defValue_2240_ = lean_ctor_get(v_opt_2238_, 1);
v_map_2241_ = lean_ctor_get(v_opts_2237_, 0);
v___x_2242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2241_, v_name_2239_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_inc(v_defValue_2240_);
return v_defValue_2240_;
}
else
{
lean_object* v_val_2243_; 
v_val_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_val_2243_);
lean_dec_ref_known(v___x_2242_, 1);
if (lean_obj_tag(v_val_2243_) == 3)
{
lean_object* v_v_2244_; 
v_v_2244_ = lean_ctor_get(v_val_2243_, 0);
lean_inc(v_v_2244_);
lean_dec_ref_known(v_val_2243_, 1);
return v_v_2244_;
}
else
{
lean_dec(v_val_2243_);
lean_inc(v_defValue_2240_);
return v_defValue_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___boxed(lean_object* v_opts_2245_, lean_object* v_opt_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2245_, v_opt_2246_);
lean_dec_ref(v_opt_2246_);
lean_dec_ref(v_opts_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object* v_x_2248_){
_start:
{
if (lean_obj_tag(v_x_2248_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v_x_2248_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_x_2248_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v_x_2248_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v_x_2248_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set_tag(v___x_2252_, 1);
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v_x_2248_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_x_2248_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v_x_2248_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v_x_2248_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 0);
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg___boxed(lean_object* v_x_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(size_t v_sz_2269_, size_t v_i_2270_, lean_object* v_bs_2271_){
_start:
{
uint8_t v___x_2272_; 
v___x_2272_ = lean_usize_dec_lt(v_i_2270_, v_sz_2269_);
if (v___x_2272_ == 0)
{
return v_bs_2271_;
}
else
{
lean_object* v_v_2273_; lean_object* v_msg_2274_; lean_object* v___x_2275_; lean_object* v_bs_x27_2276_; size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
v_v_2273_ = lean_array_uget_borrowed(v_bs_2271_, v_i_2270_);
v_msg_2274_ = lean_ctor_get(v_v_2273_, 1);
lean_inc_ref(v_msg_2274_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v_bs_x27_2276_ = lean_array_uset(v_bs_2271_, v_i_2270_, v___x_2275_);
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_add(v_i_2270_, v___x_2277_);
v___x_2279_ = lean_array_uset(v_bs_x27_2276_, v_i_2270_, v_msg_2274_);
v_i_2270_ = v___x_2278_;
v_bs_2271_ = v___x_2279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_2281_, lean_object* v_i_2282_, lean_object* v_bs_2283_){
_start:
{
size_t v_sz_boxed_2284_; size_t v_i_boxed_2285_; lean_object* v_res_2286_; 
v_sz_boxed_2284_ = lean_unbox_usize(v_sz_2281_);
lean_dec(v_sz_2281_);
v_i_boxed_2285_ = lean_unbox_usize(v_i_2282_);
lean_dec(v_i_2282_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_boxed_2284_, v_i_boxed_2285_, v_bs_2283_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(lean_object* v_oldTraces_2287_, lean_object* v_data_2288_, lean_object* v_ref_2289_, lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_fileName_2296_; lean_object* v_fileMap_2297_; lean_object* v_options_2298_; lean_object* v_currRecDepth_2299_; lean_object* v_maxRecDepth_2300_; lean_object* v_ref_2301_; lean_object* v_currNamespace_2302_; lean_object* v_openDecls_2303_; lean_object* v_initHeartbeats_2304_; lean_object* v_maxHeartbeats_2305_; lean_object* v_quotContext_2306_; lean_object* v_currMacroScope_2307_; uint8_t v_diag_2308_; lean_object* v_cancelTk_x3f_2309_; uint8_t v_suppressElabErrors_2310_; lean_object* v_inheritedTraceOptions_2311_; lean_object* v___x_2312_; lean_object* v_traceState_2313_; lean_object* v_traces_2314_; lean_object* v_ref_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; size_t v_sz_2318_; size_t v___x_2319_; lean_object* v___x_2320_; lean_object* v_msg_2321_; lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2360_; 
v_fileName_2296_ = lean_ctor_get(v___y_2293_, 0);
v_fileMap_2297_ = lean_ctor_get(v___y_2293_, 1);
v_options_2298_ = lean_ctor_get(v___y_2293_, 2);
v_currRecDepth_2299_ = lean_ctor_get(v___y_2293_, 3);
v_maxRecDepth_2300_ = lean_ctor_get(v___y_2293_, 4);
v_ref_2301_ = lean_ctor_get(v___y_2293_, 5);
v_currNamespace_2302_ = lean_ctor_get(v___y_2293_, 6);
v_openDecls_2303_ = lean_ctor_get(v___y_2293_, 7);
v_initHeartbeats_2304_ = lean_ctor_get(v___y_2293_, 8);
v_maxHeartbeats_2305_ = lean_ctor_get(v___y_2293_, 9);
v_quotContext_2306_ = lean_ctor_get(v___y_2293_, 10);
v_currMacroScope_2307_ = lean_ctor_get(v___y_2293_, 11);
v_diag_2308_ = lean_ctor_get_uint8(v___y_2293_, sizeof(void*)*14);
v_cancelTk_x3f_2309_ = lean_ctor_get(v___y_2293_, 12);
v_suppressElabErrors_2310_ = lean_ctor_get_uint8(v___y_2293_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2311_ = lean_ctor_get(v___y_2293_, 13);
v___x_2312_ = lean_st_ref_get(v___y_2294_);
v_traceState_2313_ = lean_ctor_get(v___x_2312_, 4);
lean_inc_ref(v_traceState_2313_);
lean_dec(v___x_2312_);
v_traces_2314_ = lean_ctor_get(v_traceState_2313_, 0);
lean_inc_ref(v_traces_2314_);
lean_dec_ref(v_traceState_2313_);
v_ref_2315_ = l_Lean_replaceRef(v_ref_2289_, v_ref_2301_);
lean_inc_ref(v_inheritedTraceOptions_2311_);
lean_inc(v_cancelTk_x3f_2309_);
lean_inc(v_currMacroScope_2307_);
lean_inc(v_quotContext_2306_);
lean_inc(v_maxHeartbeats_2305_);
lean_inc(v_initHeartbeats_2304_);
lean_inc(v_openDecls_2303_);
lean_inc(v_currNamespace_2302_);
lean_inc(v_maxRecDepth_2300_);
lean_inc(v_currRecDepth_2299_);
lean_inc_ref(v_options_2298_);
lean_inc_ref(v_fileMap_2297_);
lean_inc_ref(v_fileName_2296_);
v___x_2316_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2316_, 0, v_fileName_2296_);
lean_ctor_set(v___x_2316_, 1, v_fileMap_2297_);
lean_ctor_set(v___x_2316_, 2, v_options_2298_);
lean_ctor_set(v___x_2316_, 3, v_currRecDepth_2299_);
lean_ctor_set(v___x_2316_, 4, v_maxRecDepth_2300_);
lean_ctor_set(v___x_2316_, 5, v_ref_2315_);
lean_ctor_set(v___x_2316_, 6, v_currNamespace_2302_);
lean_ctor_set(v___x_2316_, 7, v_openDecls_2303_);
lean_ctor_set(v___x_2316_, 8, v_initHeartbeats_2304_);
lean_ctor_set(v___x_2316_, 9, v_maxHeartbeats_2305_);
lean_ctor_set(v___x_2316_, 10, v_quotContext_2306_);
lean_ctor_set(v___x_2316_, 11, v_currMacroScope_2307_);
lean_ctor_set(v___x_2316_, 12, v_cancelTk_x3f_2309_);
lean_ctor_set(v___x_2316_, 13, v_inheritedTraceOptions_2311_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14, v_diag_2308_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 1, v_suppressElabErrors_2310_);
v___x_2317_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2314_);
lean_dec_ref(v_traces_2314_);
v_sz_2318_ = lean_array_size(v___x_2317_);
v___x_2319_ = ((size_t)0ULL);
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_2318_, v___x_2319_, v___x_2317_);
v_msg_2321_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2321_, 0, v_data_2288_);
lean_ctor_set(v_msg_2321_, 1, v_msg_2290_);
lean_ctor_set(v_msg_2321_, 2, v___x_2320_);
v___x_2322_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_2321_, v___y_2291_, v___y_2292_, v___x_2316_, v___y_2294_);
lean_dec_ref_known(v___x_2316_, 14);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2360_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2360_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v_traceState_2328_; lean_object* v_env_2329_; lean_object* v_nextMacroScope_2330_; lean_object* v_ngen_2331_; lean_object* v_auxDeclNGen_2332_; lean_object* v_cache_2333_; lean_object* v_messages_2334_; lean_object* v_infoState_2335_; lean_object* v_snapshotTasks_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2359_; 
v___x_2327_ = lean_st_ref_take(v___y_2294_);
v_traceState_2328_ = lean_ctor_get(v___x_2327_, 4);
v_env_2329_ = lean_ctor_get(v___x_2327_, 0);
v_nextMacroScope_2330_ = lean_ctor_get(v___x_2327_, 1);
v_ngen_2331_ = lean_ctor_get(v___x_2327_, 2);
v_auxDeclNGen_2332_ = lean_ctor_get(v___x_2327_, 3);
v_cache_2333_ = lean_ctor_get(v___x_2327_, 5);
v_messages_2334_ = lean_ctor_get(v___x_2327_, 6);
v_infoState_2335_ = lean_ctor_get(v___x_2327_, 7);
v_snapshotTasks_2336_ = lean_ctor_get(v___x_2327_, 8);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2338_ = v___x_2327_;
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_snapshotTasks_2336_);
lean_inc(v_infoState_2335_);
lean_inc(v_messages_2334_);
lean_inc(v_cache_2333_);
lean_inc(v_traceState_2328_);
lean_inc(v_auxDeclNGen_2332_);
lean_inc(v_ngen_2331_);
lean_inc(v_nextMacroScope_2330_);
lean_inc(v_env_2329_);
lean_dec(v___x_2327_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
uint64_t v_tid_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2357_; 
v_tid_2340_ = lean_ctor_get_uint64(v_traceState_2328_, sizeof(void*)*1);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_traceState_2328_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v_traceState_2328_, 0);
lean_dec(v_unused_2358_);
v___x_2342_ = v_traceState_2328_;
v_isShared_2343_ = v_isSharedCheck_2357_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v_traceState_2328_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2357_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_ref_2289_);
lean_ctor_set(v___x_2344_, 1, v_a_2323_);
v___x_2345_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2287_, v___x_2344_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2345_);
v___x_2347_ = v___x_2342_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2345_);
lean_ctor_set_uint64(v_reuseFailAlloc_2356_, sizeof(void*)*1, v_tid_2340_);
v___x_2347_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 4, v___x_2347_);
v___x_2349_ = v___x_2338_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_env_2329_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_nextMacroScope_2330_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_ngen_2331_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v_auxDeclNGen_2332_);
lean_ctor_set(v_reuseFailAlloc_2355_, 4, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2355_, 5, v_cache_2333_);
lean_ctor_set(v_reuseFailAlloc_2355_, 6, v_messages_2334_);
lean_ctor_set(v_reuseFailAlloc_2355_, 7, v_infoState_2335_);
lean_ctor_set(v_reuseFailAlloc_2355_, 8, v_snapshotTasks_2336_);
v___x_2349_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2350_ = lean_st_ref_put(v___y_2294_, v___x_2349_);
v___x_2351_ = lean_box(0);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2351_);
v___x_2353_ = v___x_2325_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg___boxed(lean_object* v_oldTraces_2361_, lean_object* v_data_2362_, lean_object* v_ref_2363_, lean_object* v_msg_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2361_, v_data_2362_, v_ref_2363_, v_msg_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2370_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2374_; double v___x_2375_; 
v___x_2374_ = lean_unsigned_to_nat(1000u);
v___x_2375_ = lean_float_of_nat(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object* v_cls_2376_, uint8_t v_collapsed_2377_, lean_object* v_tag_2378_, lean_object* v_opts_2379_, uint8_t v_clsEnabled_2380_, lean_object* v_oldTraces_2381_, lean_object* v_msg_2382_, lean_object* v_resStartStop_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_fst_2391_; lean_object* v_snd_2392_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v_data_2396_; lean_object* v_fst_2399_; lean_object* v_snd_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; lean_object* v___y_2404_; lean_object* v_a_2405_; uint8_t v___y_2420_; double v___y_2451_; 
v_fst_2391_ = lean_ctor_get(v_resStartStop_2383_, 0);
lean_inc(v_fst_2391_);
v_snd_2392_ = lean_ctor_get(v_resStartStop_2383_, 1);
lean_inc(v_snd_2392_);
lean_dec_ref(v_resStartStop_2383_);
v_fst_2399_ = lean_ctor_get(v_snd_2392_, 0);
lean_inc(v_fst_2399_);
v_snd_2400_ = lean_ctor_get(v_snd_2392_, 1);
lean_inc(v_snd_2400_);
lean_dec(v_snd_2392_);
v___x_2401_ = l_Lean_trace_profiler;
v___x_2402_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2379_, v___x_2401_);
if (v___x_2402_ == 0)
{
v___y_2420_ = v___x_2402_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2457_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2379_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; double v___x_2460_; double v___x_2461_; double v___x_2462_; 
v___x_2458_ = l_Lean_trace_profiler_threshold;
v___x_2459_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2379_, v___x_2458_);
v___x_2460_ = lean_float_of_nat(v___x_2459_);
v___x_2461_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_2462_ = lean_float_div(v___x_2460_, v___x_2461_);
v___y_2451_ = v___x_2462_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; double v___x_2465_; 
v___x_2463_ = l_Lean_trace_profiler_threshold;
v___x_2464_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2379_, v___x_2463_);
v___x_2465_ = lean_float_of_nat(v___x_2464_);
v___y_2451_ = v___x_2465_;
goto v___jp_2450_;
}
}
v___jp_2393_:
{
lean_object* v___x_2397_; 
lean_inc(v___y_2395_);
v___x_2397_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2381_, v_data_2396_, v___y_2395_, v___y_2394_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2398_; 
lean_dec_ref_known(v___x_2397_, 1);
v___x_2398_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2391_);
return v___x_2398_;
}
else
{
lean_dec(v_fst_2391_);
return v___x_2397_;
}
}
v___jp_2403_:
{
uint8_t v_result_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; double v___x_2409_; lean_object* v_data_2410_; 
v_result_2406_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_fst_2391_);
v___x_2407_ = lean_box(v_result_2406_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2378_);
lean_inc_ref(v___x_2408_);
lean_inc(v_cls_2376_);
v_data_2410_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2410_, 0, v_cls_2376_);
lean_ctor_set(v_data_2410_, 1, v___x_2408_);
lean_ctor_set(v_data_2410_, 2, v_tag_2378_);
lean_ctor_set_float(v_data_2410_, sizeof(void*)*3, v___x_2409_);
lean_ctor_set_float(v_data_2410_, sizeof(void*)*3 + 8, v___x_2409_);
lean_ctor_set_uint8(v_data_2410_, sizeof(void*)*3 + 16, v_collapsed_2377_);
if (v___x_2402_ == 0)
{
lean_dec_ref_known(v___x_2408_, 1);
lean_dec(v_snd_2400_);
lean_dec(v_fst_2399_);
lean_dec_ref(v_tag_2378_);
lean_dec(v_cls_2376_);
v___y_2394_ = v_a_2405_;
v___y_2395_ = v___y_2404_;
v_data_2396_ = v_data_2410_;
goto v___jp_2393_;
}
else
{
lean_object* v_data_2411_; double v___x_2412_; double v___x_2413_; 
lean_dec_ref_known(v_data_2410_, 3);
v_data_2411_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2411_, 0, v_cls_2376_);
lean_ctor_set(v_data_2411_, 1, v___x_2408_);
lean_ctor_set(v_data_2411_, 2, v_tag_2378_);
v___x_2412_ = lean_unbox_float(v_fst_2399_);
lean_dec(v_fst_2399_);
lean_ctor_set_float(v_data_2411_, sizeof(void*)*3, v___x_2412_);
v___x_2413_ = lean_unbox_float(v_snd_2400_);
lean_dec(v_snd_2400_);
lean_ctor_set_float(v_data_2411_, sizeof(void*)*3 + 8, v___x_2413_);
lean_ctor_set_uint8(v_data_2411_, sizeof(void*)*3 + 16, v_collapsed_2377_);
v___y_2394_ = v_a_2405_;
v___y_2395_ = v___y_2404_;
v_data_2396_ = v_data_2411_;
goto v___jp_2393_;
}
}
v___jp_2414_:
{
lean_object* v_ref_2415_; lean_object* v___x_2416_; 
v_ref_2415_ = lean_ctor_get(v___y_2388_, 5);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2386_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc(v_fst_2391_);
v___x_2416_ = lean_apply_8(v_msg_2382_, v_fst_2391_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, lean_box(0));
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v___y_2404_ = v_ref_2415_;
v_a_2405_ = v_a_2417_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2418_; 
lean_dec_ref_known(v___x_2416_, 1);
v___x_2418_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_2404_ = v_ref_2415_;
v_a_2405_ = v___x_2418_;
goto v___jp_2403_;
}
}
v___jp_2419_:
{
if (v_clsEnabled_2380_ == 0)
{
if (v___y_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v_traceState_2422_; lean_object* v_env_2423_; lean_object* v_nextMacroScope_2424_; lean_object* v_ngen_2425_; lean_object* v_auxDeclNGen_2426_; lean_object* v_cache_2427_; lean_object* v_messages_2428_; lean_object* v_infoState_2429_; lean_object* v_snapshotTasks_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_snd_2400_);
lean_dec(v_fst_2399_);
lean_dec_ref(v_msg_2382_);
lean_dec_ref(v_tag_2378_);
lean_dec(v_cls_2376_);
v___x_2421_ = lean_st_ref_take(v___y_2389_);
v_traceState_2422_ = lean_ctor_get(v___x_2421_, 4);
v_env_2423_ = lean_ctor_get(v___x_2421_, 0);
v_nextMacroScope_2424_ = lean_ctor_get(v___x_2421_, 1);
v_ngen_2425_ = lean_ctor_get(v___x_2421_, 2);
v_auxDeclNGen_2426_ = lean_ctor_get(v___x_2421_, 3);
v_cache_2427_ = lean_ctor_get(v___x_2421_, 5);
v_messages_2428_ = lean_ctor_get(v___x_2421_, 6);
v_infoState_2429_ = lean_ctor_get(v___x_2421_, 7);
v_snapshotTasks_2430_ = lean_ctor_get(v___x_2421_, 8);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2432_ = v___x_2421_;
v_isShared_2433_ = v_isSharedCheck_2449_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_snapshotTasks_2430_);
lean_inc(v_infoState_2429_);
lean_inc(v_messages_2428_);
lean_inc(v_cache_2427_);
lean_inc(v_traceState_2422_);
lean_inc(v_auxDeclNGen_2426_);
lean_inc(v_ngen_2425_);
lean_inc(v_nextMacroScope_2424_);
lean_inc(v_env_2423_);
lean_dec(v___x_2421_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2449_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
uint64_t v_tid_2434_; lean_object* v_traces_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2448_; 
v_tid_2434_ = lean_ctor_get_uint64(v_traceState_2422_, sizeof(void*)*1);
v_traces_2435_ = lean_ctor_get(v_traceState_2422_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_traceState_2422_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2437_ = v_traceState_2422_;
v_isShared_2438_ = v_isSharedCheck_2448_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_traces_2435_);
lean_dec(v_traceState_2422_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2448_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2439_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2381_, v_traces_2435_);
lean_dec_ref(v_traces_2435_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2439_);
lean_ctor_set_uint64(v_reuseFailAlloc_2447_, sizeof(void*)*1, v_tid_2434_);
v___x_2441_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2443_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 4, v___x_2441_);
v___x_2443_ = v___x_2432_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_env_2423_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_nextMacroScope_2424_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_ngen_2425_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_auxDeclNGen_2426_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2446_, 5, v_cache_2427_);
lean_ctor_set(v_reuseFailAlloc_2446_, 6, v_messages_2428_);
lean_ctor_set(v_reuseFailAlloc_2446_, 7, v_infoState_2429_);
lean_ctor_set(v_reuseFailAlloc_2446_, 8, v_snapshotTasks_2430_);
v___x_2443_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_st_ref_put(v___y_2389_, v___x_2443_);
v___x_2445_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2391_);
return v___x_2445_;
}
}
}
}
}
else
{
goto v___jp_2414_;
}
}
else
{
goto v___jp_2414_;
}
}
v___jp_2450_:
{
double v___x_2452_; double v___x_2453_; double v___x_2454_; uint8_t v___x_2455_; 
v___x_2452_ = lean_unbox_float(v_snd_2400_);
v___x_2453_ = lean_unbox_float(v_fst_2399_);
v___x_2454_ = lean_float_sub(v___x_2452_, v___x_2453_);
v___x_2455_ = lean_float_decLt(v___y_2451_, v___x_2454_);
v___y_2420_ = v___x_2455_;
goto v___jp_2419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object* v_cls_2466_, lean_object* v_collapsed_2467_, lean_object* v_tag_2468_, lean_object* v_opts_2469_, lean_object* v_clsEnabled_2470_, lean_object* v_oldTraces_2471_, lean_object* v_msg_2472_, lean_object* v_resStartStop_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_collapsed_boxed_2481_; uint8_t v_clsEnabled_boxed_2482_; lean_object* v_res_2483_; 
v_collapsed_boxed_2481_ = lean_unbox(v_collapsed_2467_);
v_clsEnabled_boxed_2482_ = lean_unbox(v_clsEnabled_2470_);
v_res_2483_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_cls_2466_, v_collapsed_boxed_2481_, v_tag_2468_, v_opts_2469_, v_clsEnabled_boxed_2482_, v_oldTraces_2471_, v_msg_2472_, v_resStartStop_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_opts_2469_);
return v_res_2483_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_keys_2484_, lean_object* v_i_2485_, lean_object* v_k_2486_){
_start:
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = lean_array_get_size(v_keys_2484_);
v___x_2488_ = lean_nat_dec_lt(v_i_2485_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_dec(v_i_2485_);
return v___x_2488_;
}
else
{
lean_object* v_k_x27_2489_; uint8_t v___x_2490_; 
v_k_x27_2489_ = lean_array_fget_borrowed(v_keys_2484_, v_i_2485_);
v___x_2490_ = l_Lean_instBEqMVarId_beq(v_k_2486_, v_k_x27_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_add(v_i_2485_, v___x_2491_);
lean_dec(v_i_2485_);
v_i_2485_ = v___x_2492_;
goto _start;
}
else
{
lean_dec(v_i_2485_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_keys_2494_, lean_object* v_i_2495_, lean_object* v_k_2496_){
_start:
{
uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_res_2497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2494_, v_i_2495_, v_k_2496_);
lean_dec(v_k_2496_);
lean_dec_ref(v_keys_2494_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(lean_object* v_x_2499_, size_t v_x_2500_, lean_object* v_x_2501_){
_start:
{
if (lean_obj_tag(v_x_2499_) == 0)
{
lean_object* v_es_2502_; lean_object* v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; lean_object* v_j_2506_; lean_object* v___x_2507_; 
v_es_2502_ = lean_ctor_get(v_x_2499_, 0);
v___x_2503_ = lean_box(2);
v___x_2504_ = ((size_t)31ULL);
v___x_2505_ = lean_usize_land(v_x_2500_, v___x_2504_);
v_j_2506_ = lean_usize_to_nat(v___x_2505_);
v___x_2507_ = lean_array_get_borrowed(v___x_2503_, v_es_2502_, v_j_2506_);
lean_dec(v_j_2506_);
switch(lean_obj_tag(v___x_2507_))
{
case 0:
{
lean_object* v_key_2508_; uint8_t v___x_2509_; 
v_key_2508_ = lean_ctor_get(v___x_2507_, 0);
v___x_2509_ = l_Lean_instBEqMVarId_beq(v_x_2501_, v_key_2508_);
return v___x_2509_;
}
case 1:
{
lean_object* v_node_2510_; size_t v___x_2511_; size_t v___x_2512_; 
v_node_2510_ = lean_ctor_get(v___x_2507_, 0);
v___x_2511_ = ((size_t)5ULL);
v___x_2512_ = lean_usize_shift_right(v_x_2500_, v___x_2511_);
v_x_2499_ = v_node_2510_;
v_x_2500_ = v___x_2512_;
goto _start;
}
default: 
{
uint8_t v___x_2514_; 
v___x_2514_ = 0;
return v___x_2514_;
}
}
}
else
{
lean_object* v_ks_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_ks_2515_ = lean_ctor_get(v_x_2499_, 0);
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_ks_2515_, v___x_2516_, v_x_2501_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
size_t v_x_19067__boxed_2521_; uint8_t v_res_2522_; lean_object* v_r_2523_; 
v_x_19067__boxed_2521_ = lean_unbox_usize(v_x_2519_);
lean_dec(v_x_2519_);
v_res_2522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2518_, v_x_19067__boxed_2521_, v_x_2520_);
lean_dec(v_x_2520_);
lean_dec_ref(v_x_2518_);
v_r_2523_ = lean_box(v_res_2522_);
return v_r_2523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
uint64_t v___x_2526_; size_t v___x_2527_; uint8_t v___x_2528_; 
v___x_2526_ = l_Lean_instHashableMVarId_hash(v_x_2525_);
v___x_2527_ = lean_uint64_to_usize(v___x_2526_);
v___x_2528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2524_, v___x_2527_, v_x_2525_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg___boxed(lean_object* v_x_2529_, lean_object* v_x_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2529_, v_x_2530_);
lean_dec(v_x_2530_);
lean_dec_ref(v_x_2529_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(lean_object* v_mvarId_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v_mctx_2537_; lean_object* v_eAssignment_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2536_ = lean_st_ref_get(v___y_2534_);
v_mctx_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_mctx_2537_);
lean_dec(v___x_2536_);
v_eAssignment_2538_ = lean_ctor_get(v_mctx_2537_, 8);
lean_inc_ref(v_eAssignment_2538_);
lean_dec_ref(v_mctx_2537_);
v___x_2539_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_eAssignment_2538_, v_mvarId_2533_);
lean_dec_ref(v_eAssignment_2538_);
v___x_2540_ = lean_box(v___x_2539_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg___boxed(lean_object* v_mvarId_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec(v_mvarId_2542_);
return v_res_2545_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2546_; double v___x_2547_; 
v___x_2546_ = lean_unsigned_to_nat(1000000000u);
v___x_2547_ = lean_float_of_nat(v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1));
v___x_2550_ = l_Lean_stringToMessageData(v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(lean_object* v___x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v___x_2551_, v___y_2555_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2729_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2729_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2729_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_del_object(v___x_2562_);
lean_inc(v___x_2551_);
v___x_2565_ = l_Lean_MVarId_getType(v___x_2551_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_options_2566_; uint8_t v_hasTrace_2567_; 
v_options_2566_ = lean_ctor_get(v___y_2556_, 2);
v_hasTrace_2567_ = lean_ctor_get_uint8(v_options_2566_, sizeof(void*)*1);
if (v_hasTrace_2567_ == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; 
v_a_2568_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2569_ = l_Lean_Meta_mkDefault(v_a_2568_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2551_, v_a_2570_, v___y_2555_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2579_; 
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2571_, 0);
lean_dec(v_unused_2580_);
v___x_2573_ = v___x_2571_;
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v___x_2571_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_box(0);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2575_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
return v___x_2571_;
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v___x_2551_);
v_a_2581_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2569_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2569_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v_inheritedTraceOptions_2590_; lean_object* v___f_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v_a_2599_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v_a_2614_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v_a_2619_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v_a_2630_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v_a_2642_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v_a_2647_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; 
v_a_2589_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_n(v_a_2589_, 2);
lean_dec_ref_known(v___x_2565_, 1);
v_inheritedTraceOptions_2590_ = lean_ctor_get(v___y_2556_, 13);
v___f_2591_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2591_, 0, v_a_2589_);
v___x_2592_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2593_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_2594_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2590_, v_options_2566_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = l_Lean_trace_profiler;
v___x_2691_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2566_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; 
lean_dec_ref(v___f_2591_);
v___x_2692_ = l_Lean_Meta_mkDefault(v_a_2589_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc_n(v_a_2693_, 2);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2551_, v_a_2693_, v___y_2555_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2707_; 
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v___x_2694_, 0);
lean_dec(v_unused_2708_);
v___x_2696_ = v___x_2694_;
v_isShared_2697_ = v_isSharedCheck_2707_;
goto v_resetjp_2695_;
}
else
{
lean_dec(v___x_2694_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2707_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
if (v___x_2595_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec(v_a_2693_);
v___x_2698_ = lean_box(0);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2698_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2696_);
v___x_2702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2703_ = lean_unsigned_to_nat(30u);
v___x_2704_ = l_Lean_inlineExprTrailing(v_a_2693_, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2702_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2592_, v___x_2705_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2706_;
}
}
}
else
{
lean_dec(v_a_2693_);
return v___x_2694_;
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v___x_2551_);
v_a_2709_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2692_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2692_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
goto v___jp_2655_;
}
}
else
{
goto v___jp_2655_;
}
v___jp_2596_:
{
lean_object* v___x_2600_; double v___x_2601_; double v___x_2602_; double v___x_2603_; double v___x_2604_; double v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2600_ = lean_io_mono_nanos_now();
v___x_2601_ = lean_float_of_nat(v___y_2598_);
v___x_2602_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_2603_ = lean_float_div(v___x_2601_, v___x_2602_);
v___x_2604_ = lean_float_of_nat(v___x_2600_);
v___x_2605_ = lean_float_div(v___x_2604_, v___x_2602_);
v___x_2606_ = lean_box_float(v___x_2603_);
v___x_2607_ = lean_box_float(v___x_2605_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_a_2599_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2592_, v_hasTrace_2567_, v___x_2593_, v_options_2566_, v___x_2595_, v___y_2597_, v___f_2591_, v___x_2609_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2610_;
}
v___jp_2611_:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_a_2614_);
v___y_2597_ = v___y_2612_;
v___y_2598_ = v___y_2613_;
v_a_2599_ = v___x_2615_;
goto v___jp_2596_;
}
v___jp_2616_:
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2620_, 0, v_a_2619_);
v___y_2597_ = v___y_2617_;
v___y_2598_ = v___y_2618_;
v_a_2599_ = v___x_2620_;
goto v___jp_2596_;
}
v___jp_2621_:
{
if (lean_obj_tag(v___y_2624_) == 0)
{
lean_object* v_a_2625_; 
v_a_2625_ = lean_ctor_get(v___y_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___y_2624_, 1);
v___y_2617_ = v___y_2622_;
v___y_2618_ = v___y_2623_;
v_a_2619_ = v_a_2625_;
goto v___jp_2616_;
}
else
{
lean_object* v_a_2626_; 
v_a_2626_ = lean_ctor_get(v___y_2624_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___y_2624_, 1);
v___y_2612_ = v___y_2622_;
v___y_2613_ = v___y_2623_;
v_a_2614_ = v_a_2626_;
goto v___jp_2611_;
}
}
v___jp_2627_:
{
lean_object* v___x_2631_; double v___x_2632_; double v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2631_ = lean_io_get_num_heartbeats();
v___x_2632_ = lean_float_of_nat(v___y_2629_);
v___x_2633_ = lean_float_of_nat(v___x_2631_);
v___x_2634_ = lean_box_float(v___x_2632_);
v___x_2635_ = lean_box_float(v___x_2633_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2634_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v_a_2630_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2592_, v_hasTrace_2567_, v___x_2593_, v_options_2566_, v___x_2595_, v___y_2628_, v___f_2591_, v___x_2637_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2638_;
}
v___jp_2639_:
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_a_2642_);
v___y_2628_ = v___y_2640_;
v___y_2629_ = v___y_2641_;
v_a_2630_ = v___x_2643_;
goto v___jp_2627_;
}
v___jp_2644_:
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_a_2647_);
v___y_2628_ = v___y_2645_;
v___y_2629_ = v___y_2646_;
v_a_2630_ = v___x_2648_;
goto v___jp_2627_;
}
v___jp_2649_:
{
if (lean_obj_tag(v___y_2652_) == 0)
{
lean_object* v_a_2653_; 
v_a_2653_ = lean_ctor_get(v___y_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___y_2652_, 1);
v___y_2645_ = v___y_2650_;
v___y_2646_ = v___y_2651_;
v_a_2647_ = v_a_2653_;
goto v___jp_2644_;
}
else
{
lean_object* v_a_2654_; 
v_a_2654_ = lean_ctor_get(v___y_2652_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___y_2652_, 1);
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
v_a_2642_ = v_a_2654_;
goto v___jp_2639_;
}
}
v___jp_2655_:
{
lean_object* v___x_2656_; 
v___x_2656_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_2557_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2659_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2566_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_io_mono_nanos_now();
v___x_2661_ = l_Lean_Meta_mkDefault(v_a_2589_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2663_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc_n(v_a_2662_, 2);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2551_, v_a_2662_, v___y_2555_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_dec_ref_known(v___x_2663_, 1);
if (v___x_2595_ == 0)
{
lean_object* v___x_2664_; 
lean_dec(v_a_2662_);
v___x_2664_ = lean_box(0);
v___y_2617_ = v_a_2657_;
v___y_2618_ = v___x_2660_;
v_a_2619_ = v___x_2664_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2666_ = lean_unsigned_to_nat(30u);
v___x_2667_ = l_Lean_inlineExprTrailing(v_a_2662_, v___x_2666_);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2665_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2592_, v___x_2668_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
v___y_2622_ = v_a_2657_;
v___y_2623_ = v___x_2660_;
v___y_2624_ = v___x_2669_;
goto v___jp_2621_;
}
}
else
{
lean_dec(v_a_2662_);
v___y_2622_ = v_a_2657_;
v___y_2623_ = v___x_2660_;
v___y_2624_ = v___x_2663_;
goto v___jp_2621_;
}
}
else
{
lean_object* v_a_2670_; 
lean_dec(v___x_2551_);
v_a_2670_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2661_, 1);
v___y_2612_ = v_a_2657_;
v___y_2613_ = v___x_2660_;
v_a_2614_ = v_a_2670_;
goto v___jp_2611_;
}
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_io_get_num_heartbeats();
v___x_2672_ = l_Lean_Meta_mkDefault(v_a_2589_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_n(v_a_2673_, 2);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2551_, v_a_2673_, v___y_2555_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_dec_ref_known(v___x_2674_, 1);
if (v___x_2595_ == 0)
{
lean_object* v___x_2675_; 
lean_dec(v_a_2673_);
v___x_2675_ = lean_box(0);
v___y_2645_ = v_a_2657_;
v___y_2646_ = v___x_2671_;
v_a_2647_ = v___x_2675_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2677_ = lean_unsigned_to_nat(30u);
v___x_2678_ = l_Lean_inlineExprTrailing(v_a_2673_, v___x_2677_);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2676_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2592_, v___x_2679_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
v___y_2650_ = v_a_2657_;
v___y_2651_ = v___x_2671_;
v___y_2652_ = v___x_2680_;
goto v___jp_2649_;
}
}
else
{
lean_dec(v_a_2673_);
v___y_2650_ = v_a_2657_;
v___y_2651_ = v___x_2671_;
v___y_2652_ = v___x_2674_;
goto v___jp_2649_;
}
}
else
{
lean_object* v_a_2681_; 
lean_dec(v___x_2551_);
v_a_2681_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2672_, 1);
v___y_2640_ = v_a_2657_;
v___y_2641_ = v___x_2671_;
v_a_2642_ = v_a_2681_;
goto v___jp_2639_;
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref(v___f_2591_);
lean_dec(v_a_2589_);
lean_dec(v___x_2551_);
v_a_2682_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2656_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2656_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v___x_2551_);
v_a_2717_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2565_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2565_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_dec(v___x_2551_);
v___x_2725_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2725_);
v___x_2727_ = v___x_2562_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v___x_2551_);
v_a_2730_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2559_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2559_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2747_, size_t v_i_2748_, size_t v_stop_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
uint8_t v___x_2758_; 
v___x_2758_ = lean_usize_dec_eq(v_i_2748_, v_stop_2749_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___f_2760_; lean_object* v___x_2761_; 
v___x_2759_ = lean_array_uget_borrowed(v_as_2747_, v_i_2748_);
lean_inc_n(v___x_2759_, 2);
v___f_2760_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2760_, 0, v___x_2759_);
v___x_2761_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2759_, v___f_2760_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; size_t v___x_2763_; size_t v___x_2764_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_add(v_i_2748_, v___x_2763_);
v_i_2748_ = v___x_2764_;
v_b_2750_ = v_a_2762_;
goto _start;
}
else
{
return v___x_2761_;
}
}
else
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_b_2750_);
return v___x_2766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2767_, lean_object* v_i_2768_, lean_object* v_stop_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
size_t v_i_boxed_2778_; size_t v_stop_boxed_2779_; lean_object* v_res_2780_; 
v_i_boxed_2778_ = lean_unbox_usize(v_i_2768_);
lean_dec(v_i_2768_);
v_stop_boxed_2779_ = lean_unbox_usize(v_stop_2769_);
lean_dec(v_stop_2769_);
v_res_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2767_, v_i_boxed_2778_, v_stop_boxed_2779_, v_b_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec_ref(v_as_2767_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2781_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2811_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2811_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2811_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = lean_array_get_size(v_a_2790_);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_nat_dec_lt(v___x_2794_, v___x_2795_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2799_; 
lean_dec(v_a_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2796_);
v___x_2799_ = v___x_2792_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2796_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
else
{
uint8_t v___x_2801_; 
v___x_2801_ = lean_nat_dec_le(v___x_2795_, v___x_2795_);
if (v___x_2801_ == 0)
{
if (v___x_2797_ == 0)
{
lean_object* v___x_2803_; 
lean_dec(v_a_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2796_);
v___x_2803_ = v___x_2792_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2796_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
else
{
size_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; 
lean_del_object(v___x_2792_);
v___x_2805_ = ((size_t)0ULL);
v___x_2806_ = lean_usize_of_nat(v___x_2795_);
v___x_2807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2790_, v___x_2805_, v___x_2806_, v___x_2796_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2790_);
return v___x_2807_;
}
}
else
{
size_t v___x_2808_; size_t v___x_2809_; lean_object* v___x_2810_; 
lean_del_object(v___x_2792_);
v___x_2808_ = ((size_t)0ULL);
v___x_2809_ = lean_usize_of_nat(v___x_2795_);
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2790_, v___x_2808_, v___x_2809_, v___x_2796_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2790_);
return v___x_2810_;
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_a_2812_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2789_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2789_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2829_, v___y_2833_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v_mvarId_2838_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v_mvarId_2847_, lean_object* v_val_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2847_, v_val_2848_, v___y_2852_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v_mvarId_2857_, lean_object* v_val_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2857_, v_val_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object* v_00_u03b1_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_2868_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2877_, lean_object* v_x_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(v_00_u03b1_2877_, v_x_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2886_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
uint8_t v___x_2890_; 
v___x_2890_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2888_, v_x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_){
_start:
{
uint8_t v_res_2894_; lean_object* v_r_2895_; 
v_res_2894_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2891_, v_x_2892_, v_x_2893_);
lean_dec(v_x_2893_);
lean_dec_ref(v_x_2892_);
v_r_2895_ = lean_box(v_res_2894_);
return v_r_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object* v_00_u03b2_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_x_2897_, v_x_2898_, v_x_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object* v_oldTraces_2901_, lean_object* v_data_2902_, lean_object* v_ref_2903_, lean_object* v_msg_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2901_, v_data_2902_, v_ref_2903_, v_msg_2904_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object* v_oldTraces_2913_, lean_object* v_data_2914_, lean_object* v_ref_2915_, lean_object* v_msg_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_oldTraces_2913_, v_data_2914_, v_ref_2915_, v_msg_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2924_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2925_, lean_object* v_x_2926_, size_t v_x_2927_, lean_object* v_x_2928_){
_start:
{
uint8_t v___x_2929_; 
v___x_2929_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2926_, v_x_2927_, v_x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2930_, lean_object* v_x_2931_, lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
size_t v_x_19766__boxed_2934_; uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_x_19766__boxed_2934_ = lean_unbox_usize(v_x_2932_);
lean_dec(v_x_2932_);
v_res_2935_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2930_, v_x_2931_, v_x_19766__boxed_2934_, v_x_2933_);
lean_dec(v_x_2933_);
lean_dec_ref(v_x_2931_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2937_, lean_object* v_x_2938_, size_t v_x_2939_, size_t v_x_2940_, lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2938_, v_x_2939_, v_x_2940_, v_x_2941_, v_x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
size_t v_x_19777__boxed_2950_; size_t v_x_19778__boxed_2951_; lean_object* v_res_2952_; 
v_x_19777__boxed_2950_ = lean_unbox_usize(v_x_2946_);
lean_dec(v_x_2946_);
v_x_19778__boxed_2951_ = lean_unbox_usize(v_x_2947_);
lean_dec(v_x_2947_);
v_res_2952_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(v_00_u03b2_2944_, v_x_2945_, v_x_19777__boxed_2950_, v_x_19778__boxed_2951_, v_x_2948_, v_x_2949_);
return v_res_2952_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2953_, lean_object* v_keys_2954_, lean_object* v_vals_2955_, lean_object* v_heq_2956_, lean_object* v_i_2957_, lean_object* v_k_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2954_, v_i_2957_, v_k_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2960_, lean_object* v_keys_2961_, lean_object* v_vals_2962_, lean_object* v_heq_2963_, lean_object* v_i_2964_, lean_object* v_k_2965_){
_start:
{
uint8_t v_res_2966_; lean_object* v_r_2967_; 
v_res_2966_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2960_, v_keys_2961_, v_vals_2962_, v_heq_2963_, v_i_2964_, v_k_2965_);
lean_dec(v_k_2965_);
lean_dec_ref(v_vals_2962_);
lean_dec_ref(v_keys_2961_);
v_r_2967_ = lean_box(v_res_2966_);
return v_r_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_2968_, lean_object* v_n_2969_, lean_object* v_k_2970_, lean_object* v_v_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v_n_2969_, v_k_2970_, v_v_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b2_2973_, size_t v_depth_2974_, lean_object* v_keys_2975_, lean_object* v_vals_2976_, lean_object* v_heq_2977_, lean_object* v_i_2978_, lean_object* v_entries_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2974_, v_keys_2975_, v_vals_2976_, v_i_2978_, v_entries_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b2_2981_, lean_object* v_depth_2982_, lean_object* v_keys_2983_, lean_object* v_vals_2984_, lean_object* v_heq_2985_, lean_object* v_i_2986_, lean_object* v_entries_2987_){
_start:
{
size_t v_depth_boxed_2988_; lean_object* v_res_2989_; 
v_depth_boxed_2988_ = lean_unbox_usize(v_depth_2982_);
lean_dec(v_depth_2982_);
v_res_2989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(v_00_u03b2_2981_, v_depth_boxed_2988_, v_keys_2983_, v_vals_2984_, v_heq_2985_, v_i_2986_, v_entries_2987_);
lean_dec_ref(v_vals_2984_);
lean_dec_ref(v_keys_2983_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_x_2991_, v_x_2992_, v_x_2993_, v_x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = l_Lean_Expr_hasMVar(v_e_2996_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_e_2996_);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; lean_object* v_mctx_3002_; lean_object* v___x_3003_; lean_object* v_fst_3004_; lean_object* v_snd_3005_; lean_object* v___x_3006_; lean_object* v_cache_3007_; lean_object* v_zetaDeltaFVarIds_3008_; lean_object* v_postponed_3009_; lean_object* v_diag_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3019_; 
v___x_3001_ = lean_st_ref_get(v___y_2997_);
v_mctx_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc_ref(v_mctx_3002_);
lean_dec(v___x_3001_);
v___x_3003_ = l_Lean_instantiateMVarsCore(v_mctx_3002_, v_e_2996_);
v_fst_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_fst_3004_);
v_snd_3005_ = lean_ctor_get(v___x_3003_, 1);
lean_inc(v_snd_3005_);
lean_dec_ref(v___x_3003_);
v___x_3006_ = lean_st_ref_take(v___y_2997_);
v_cache_3007_ = lean_ctor_get(v___x_3006_, 1);
v_zetaDeltaFVarIds_3008_ = lean_ctor_get(v___x_3006_, 2);
v_postponed_3009_ = lean_ctor_get(v___x_3006_, 3);
v_diag_3010_ = lean_ctor_get(v___x_3006_, 4);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v___x_3006_, 0);
lean_dec(v_unused_3020_);
v___x_3012_ = v___x_3006_;
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_diag_3010_);
lean_inc(v_postponed_3009_);
lean_inc(v_zetaDeltaFVarIds_3008_);
lean_inc(v_cache_3007_);
lean_dec(v___x_3006_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v_snd_3005_);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_snd_3005_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_cache_3007_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_zetaDeltaFVarIds_3008_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_postponed_3009_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_diag_3010_);
v___x_3015_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_st_ref_put(v___y_2997_, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_fst_3004_);
return v___x_3017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_3021_, v___y_3022_);
lean_dec(v___y_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_3025_, v___y_3029_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3042_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_24906__overap_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_24906__overap_3053_ = lean_panic_fn_borrowed(v___x_3052_, v_msg_3044_);
lean_inc(v___y_3050_);
lean_inc_ref(v___y_3049_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3047_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3045_);
v___x_3054_ = lean_apply_7(v___x_24906__overap_3053_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, lean_box(0));
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object* v_a_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object* v_a_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_00_u03b1_3082_, lean_object* v_a_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_00_u03b1_3092_, lean_object* v_a_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_00_u03b1_3092_, v_a_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object* v_k_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v_b_3105_, lean_object* v_c_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v___x_3112_; 
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
v___x_3112_ = lean_apply_9(v_k_3102_, v_b_3105_, v_c_3106_, v___y_3103_, v___y_3104_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, lean_box(0));
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object* v_k_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v_b_3116_, lean_object* v_c_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_3113_, v___y_3114_, v___y_3115_, v_b_3116_, v_c_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_type_3124_, lean_object* v_k_3125_, uint8_t v_cleanupAnnotations_3126_, uint8_t v_whnfType_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___f_3135_; lean_object* v___x_3136_; 
lean_inc(v___y_3129_);
lean_inc_ref(v___y_3128_);
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3135_, 0, v_k_3125_);
lean_closure_set(v___f_3135_, 1, v___y_3128_);
lean_closure_set(v___f_3135_, 2, v___y_3129_);
v___x_3136_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3124_, v___f_3135_, v_cleanupAnnotations_3126_, v_whnfType_3127_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3136_) == 0)
{
return v___x_3136_;
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_type_3145_, lean_object* v_k_3146_, lean_object* v_cleanupAnnotations_3147_, lean_object* v_whnfType_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3156_; uint8_t v_whnfType_boxed_3157_; lean_object* v_res_3158_; 
v_cleanupAnnotations_boxed_3156_ = lean_unbox(v_cleanupAnnotations_3147_);
v_whnfType_boxed_3157_ = lean_unbox(v_whnfType_3148_);
v_res_3158_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3145_, v_k_3146_, v_cleanupAnnotations_boxed_3156_, v_whnfType_boxed_3157_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_3159_, lean_object* v_type_3160_, lean_object* v_k_3161_, uint8_t v_cleanupAnnotations_3162_, uint8_t v_whnfType_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3160_, v_k_3161_, v_cleanupAnnotations_3162_, v_whnfType_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_3172_, lean_object* v_type_3173_, lean_object* v_k_3174_, lean_object* v_cleanupAnnotations_3175_, lean_object* v_whnfType_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3184_; uint8_t v_whnfType_boxed_3185_; lean_object* v_res_3186_; 
v_cleanupAnnotations_boxed_3184_ = lean_unbox(v_cleanupAnnotations_3175_);
v_whnfType_boxed_3185_ = lean_unbox(v_whnfType_3176_);
v_res_3186_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_3172_, v_type_3173_, v_k_3174_, v_cleanupAnnotations_boxed_3184_, v_whnfType_boxed_3185_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v_res_3186_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3189_ = l_Lean_stringToMessageData(v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_x_3200_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v___x_3209_, lean_object* v_fst_3210_, lean_object* v_____r_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = l_Lean_mkAppN(v___x_3209_, v_fst_3210_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v___x_3221_, lean_object* v_fst_3222_, lean_object* v_____r_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3221_, v_fst_3222_, v_____r_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v_fst_3222_);
return v_res_3231_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v_ctorName_3235_, uint8_t v___x_3236_, lean_object* v_x_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3245_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1);
v___x_3246_ = l_Lean_MessageData_ofConstName(v_ctorName_3235_, v___x_3236_);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v_ctorName_3251_, lean_object* v___x_3252_, lean_object* v_x_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v___x_29786__boxed_3261_; lean_object* v_res_3262_; 
v___x_29786__boxed_3261_ = lean_unbox(v___x_3252_);
v_res_3262_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3251_, v___x_29786__boxed_3261_, v_x_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec_ref(v_x_3253_);
return v_res_3262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object* v_e_3263_){
_start:
{
if (lean_obj_tag(v_e_3263_) == 0)
{
uint8_t v___x_3264_; 
v___x_3264_ = 2;
return v___x_3264_;
}
else
{
lean_object* v_a_3265_; uint8_t v___x_3266_; 
v_a_3265_ = lean_ctor_get(v_e_3263_, 0);
v___x_3266_ = l_Lean_Expr_hasSyntheticSorry(v_a_3265_);
if (v___x_3266_ == 0)
{
uint8_t v___x_3267_; 
v___x_3267_ = 0;
return v___x_3267_;
}
else
{
uint8_t v___x_3268_; 
v___x_3268_ = 1;
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object* v_e_3269_){
_start:
{
uint8_t v_res_3270_; lean_object* v_r_3271_; 
v_res_3270_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3269_);
lean_dec_ref(v_e_3269_);
v_r_3271_ = lean_box(v_res_3270_);
return v_r_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v_cls_3272_, uint8_t v_collapsed_3273_, lean_object* v_tag_3274_, lean_object* v_opts_3275_, uint8_t v_clsEnabled_3276_, lean_object* v_oldTraces_3277_, lean_object* v_msg_3278_, lean_object* v_resStartStop_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_fst_3287_; lean_object* v_snd_3288_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v_data_3292_; lean_object* v_fst_3303_; lean_object* v_snd_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___y_3308_; lean_object* v_a_3309_; uint8_t v___y_3324_; double v___y_3355_; 
v_fst_3287_ = lean_ctor_get(v_resStartStop_3279_, 0);
lean_inc(v_fst_3287_);
v_snd_3288_ = lean_ctor_get(v_resStartStop_3279_, 1);
lean_inc(v_snd_3288_);
lean_dec_ref(v_resStartStop_3279_);
v_fst_3303_ = lean_ctor_get(v_snd_3288_, 0);
lean_inc(v_fst_3303_);
v_snd_3304_ = lean_ctor_get(v_snd_3288_, 1);
lean_inc(v_snd_3304_);
lean_dec(v_snd_3288_);
v___x_3305_ = l_Lean_trace_profiler;
v___x_3306_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3275_, v___x_3305_);
if (v___x_3306_ == 0)
{
v___y_3324_ = v___x_3306_;
goto v___jp_3323_;
}
else
{
lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3361_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3275_, v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; double v___x_3364_; double v___x_3365_; double v___x_3366_; 
v___x_3362_ = l_Lean_trace_profiler_threshold;
v___x_3363_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3275_, v___x_3362_);
v___x_3364_ = lean_float_of_nat(v___x_3363_);
v___x_3365_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_3366_ = lean_float_div(v___x_3364_, v___x_3365_);
v___y_3355_ = v___x_3366_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; double v___x_3369_; 
v___x_3367_ = l_Lean_trace_profiler_threshold;
v___x_3368_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3275_, v___x_3367_);
v___x_3369_ = lean_float_of_nat(v___x_3368_);
v___y_3355_ = v___x_3369_;
goto v___jp_3354_;
}
}
v___jp_3289_:
{
lean_object* v___x_3293_; 
lean_inc(v___y_3291_);
v___x_3293_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_3277_, v_data_3292_, v___y_3291_, v___y_3290_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v___x_3294_; 
lean_dec_ref_known(v___x_3293_, 1);
v___x_3294_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3287_);
return v___x_3294_;
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v_fst_3287_);
v_a_3295_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3293_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3293_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
v___jp_3307_:
{
uint8_t v_result_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; double v___x_3313_; lean_object* v_data_3314_; 
v_result_3310_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_fst_3287_);
v___x_3311_ = lean_box(v_result_3310_);
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
v___x_3313_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3274_);
lean_inc_ref(v___x_3312_);
lean_inc(v_cls_3272_);
v_data_3314_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3314_, 0, v_cls_3272_);
lean_ctor_set(v_data_3314_, 1, v___x_3312_);
lean_ctor_set(v_data_3314_, 2, v_tag_3274_);
lean_ctor_set_float(v_data_3314_, sizeof(void*)*3, v___x_3313_);
lean_ctor_set_float(v_data_3314_, sizeof(void*)*3 + 8, v___x_3313_);
lean_ctor_set_uint8(v_data_3314_, sizeof(void*)*3 + 16, v_collapsed_3273_);
if (v___x_3306_ == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
lean_dec(v_snd_3304_);
lean_dec(v_fst_3303_);
lean_dec_ref(v_tag_3274_);
lean_dec(v_cls_3272_);
v___y_3290_ = v_a_3309_;
v___y_3291_ = v___y_3308_;
v_data_3292_ = v_data_3314_;
goto v___jp_3289_;
}
else
{
lean_object* v_data_3315_; double v___x_3316_; double v___x_3317_; 
lean_dec_ref_known(v_data_3314_, 3);
v_data_3315_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3315_, 0, v_cls_3272_);
lean_ctor_set(v_data_3315_, 1, v___x_3312_);
lean_ctor_set(v_data_3315_, 2, v_tag_3274_);
v___x_3316_ = lean_unbox_float(v_fst_3303_);
lean_dec(v_fst_3303_);
lean_ctor_set_float(v_data_3315_, sizeof(void*)*3, v___x_3316_);
v___x_3317_ = lean_unbox_float(v_snd_3304_);
lean_dec(v_snd_3304_);
lean_ctor_set_float(v_data_3315_, sizeof(void*)*3 + 8, v___x_3317_);
lean_ctor_set_uint8(v_data_3315_, sizeof(void*)*3 + 16, v_collapsed_3273_);
v___y_3290_ = v_a_3309_;
v___y_3291_ = v___y_3308_;
v_data_3292_ = v_data_3315_;
goto v___jp_3289_;
}
}
v___jp_3318_:
{
lean_object* v_ref_3319_; lean_object* v___x_3320_; 
v_ref_3319_ = lean_ctor_get(v___y_3284_, 5);
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3282_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
lean_inc(v_fst_3287_);
v___x_3320_ = lean_apply_8(v_msg_3278_, v_fst_3287_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, lean_box(0));
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3320_, 1);
v___y_3308_ = v_ref_3319_;
v_a_3309_ = v_a_3321_;
goto v___jp_3307_;
}
else
{
lean_object* v___x_3322_; 
lean_dec_ref_known(v___x_3320_, 1);
v___x_3322_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_3308_ = v_ref_3319_;
v_a_3309_ = v___x_3322_;
goto v___jp_3307_;
}
}
v___jp_3323_:
{
if (v_clsEnabled_3276_ == 0)
{
if (v___y_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v_traceState_3326_; lean_object* v_env_3327_; lean_object* v_nextMacroScope_3328_; lean_object* v_ngen_3329_; lean_object* v_auxDeclNGen_3330_; lean_object* v_cache_3331_; lean_object* v_messages_3332_; lean_object* v_infoState_3333_; lean_object* v_snapshotTasks_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_snd_3304_);
lean_dec(v_fst_3303_);
lean_dec_ref(v_msg_3278_);
lean_dec_ref(v_tag_3274_);
lean_dec(v_cls_3272_);
v___x_3325_ = lean_st_ref_take(v___y_3285_);
v_traceState_3326_ = lean_ctor_get(v___x_3325_, 4);
v_env_3327_ = lean_ctor_get(v___x_3325_, 0);
v_nextMacroScope_3328_ = lean_ctor_get(v___x_3325_, 1);
v_ngen_3329_ = lean_ctor_get(v___x_3325_, 2);
v_auxDeclNGen_3330_ = lean_ctor_get(v___x_3325_, 3);
v_cache_3331_ = lean_ctor_get(v___x_3325_, 5);
v_messages_3332_ = lean_ctor_get(v___x_3325_, 6);
v_infoState_3333_ = lean_ctor_get(v___x_3325_, 7);
v_snapshotTasks_3334_ = lean_ctor_get(v___x_3325_, 8);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3336_ = v___x_3325_;
v_isShared_3337_ = v_isSharedCheck_3353_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_snapshotTasks_3334_);
lean_inc(v_infoState_3333_);
lean_inc(v_messages_3332_);
lean_inc(v_cache_3331_);
lean_inc(v_traceState_3326_);
lean_inc(v_auxDeclNGen_3330_);
lean_inc(v_ngen_3329_);
lean_inc(v_nextMacroScope_3328_);
lean_inc(v_env_3327_);
lean_dec(v___x_3325_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3353_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
uint64_t v_tid_3338_; lean_object* v_traces_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3352_; 
v_tid_3338_ = lean_ctor_get_uint64(v_traceState_3326_, sizeof(void*)*1);
v_traces_3339_ = lean_ctor_get(v_traceState_3326_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_traceState_3326_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3341_ = v_traceState_3326_;
v_isShared_3342_ = v_isSharedCheck_3352_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_traces_3339_);
lean_dec(v_traceState_3326_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3352_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3277_, v_traces_3339_);
lean_dec_ref(v_traces_3339_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3343_);
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3343_);
lean_ctor_set_uint64(v_reuseFailAlloc_3351_, sizeof(void*)*1, v_tid_3338_);
v___x_3345_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 4, v___x_3345_);
v___x_3347_ = v___x_3336_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_env_3327_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_nextMacroScope_3328_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_ngen_3329_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_auxDeclNGen_3330_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3350_, 5, v_cache_3331_);
lean_ctor_set(v_reuseFailAlloc_3350_, 6, v_messages_3332_);
lean_ctor_set(v_reuseFailAlloc_3350_, 7, v_infoState_3333_);
lean_ctor_set(v_reuseFailAlloc_3350_, 8, v_snapshotTasks_3334_);
v___x_3347_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_st_ref_put(v___y_3285_, v___x_3347_);
v___x_3349_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3287_);
return v___x_3349_;
}
}
}
}
}
else
{
goto v___jp_3318_;
}
}
else
{
goto v___jp_3318_;
}
}
v___jp_3354_:
{
double v___x_3356_; double v___x_3357_; double v___x_3358_; uint8_t v___x_3359_; 
v___x_3356_ = lean_unbox_float(v_snd_3304_);
v___x_3357_ = lean_unbox_float(v_fst_3303_);
v___x_3358_ = lean_float_sub(v___x_3356_, v___x_3357_);
v___x_3359_ = lean_float_decLt(v___y_3355_, v___x_3358_);
v___y_3324_ = v___x_3359_;
goto v___jp_3323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v_cls_3370_, lean_object* v_collapsed_3371_, lean_object* v_tag_3372_, lean_object* v_opts_3373_, lean_object* v_clsEnabled_3374_, lean_object* v_oldTraces_3375_, lean_object* v_msg_3376_, lean_object* v_resStartStop_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
uint8_t v_collapsed_boxed_3385_; uint8_t v_clsEnabled_boxed_3386_; lean_object* v_res_3387_; 
v_collapsed_boxed_3385_ = lean_unbox(v_collapsed_3371_);
v_clsEnabled_boxed_3386_ = lean_unbox(v_clsEnabled_3374_);
v_res_3387_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3370_, v_collapsed_boxed_3385_, v_tag_3372_, v_opts_3373_, v_clsEnabled_boxed_3386_, v_oldTraces_3375_, v_msg_3376_, v_resStartStop_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v_opts_3373_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v___x_3388_, lean_object* v_as_3389_, size_t v_i_3390_, size_t v_stop_3391_, lean_object* v_b_3392_){
_start:
{
lean_object* v___y_3394_; uint8_t v___x_3398_; 
v___x_3398_ = lean_usize_dec_eq(v_i_3390_, v_stop_3391_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; uint8_t v___x_3400_; 
v___x_3399_ = lean_array_uget_borrowed(v_as_3389_, v_i_3390_);
v___x_3400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v___x_3388_, v___x_3399_);
if (v___x_3400_ == 0)
{
v___y_3394_ = v_b_3392_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3401_; 
lean_inc(v___x_3399_);
v___x_3401_ = lean_array_push(v_b_3392_, v___x_3399_);
v___y_3394_ = v___x_3401_;
goto v___jp_3393_;
}
}
else
{
return v_b_3392_;
}
v___jp_3393_:
{
size_t v___x_3395_; size_t v___x_3396_; 
v___x_3395_ = ((size_t)1ULL);
v___x_3396_ = lean_usize_add(v_i_3390_, v___x_3395_);
v_i_3390_ = v___x_3396_;
v_b_3392_ = v___y_3394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v___x_3402_, lean_object* v_as_3403_, lean_object* v_i_3404_, lean_object* v_stop_3405_, lean_object* v_b_3406_){
_start:
{
size_t v_i_boxed_3407_; size_t v_stop_boxed_3408_; lean_object* v_res_3409_; 
v_i_boxed_3407_ = lean_unbox_usize(v_i_3404_);
lean_dec(v_i_3404_);
v_stop_boxed_3408_ = lean_unbox_usize(v_stop_3405_);
lean_dec(v_stop_3405_);
v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3402_, v_as_3403_, v_i_boxed_3407_, v_stop_boxed_3408_, v_b_3406_);
lean_dec_ref(v_as_3403_);
lean_dec_ref(v___x_3402_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
if (lean_obj_tag(v_a_3410_) == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = l_List_reverse___redArg(v_a_3411_);
return v___x_3412_;
}
else
{
lean_object* v_head_3413_; lean_object* v_tail_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3423_; 
v_head_3413_ = lean_ctor_get(v_a_3410_, 0);
v_tail_3414_ = lean_ctor_get(v_a_3410_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_a_3410_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3416_ = v_a_3410_;
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_tail_3414_);
lean_inc(v_head_3413_);
lean_dec(v_a_3410_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = l_Lean_MessageData_ofExpr(v_head_3413_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 1, v_a_3411_);
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_a_3411_);
v___x_3420_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
v_a_3410_ = v_tail_3414_;
v_a_3411_ = v___x_3420_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3428_ = lean_unsigned_to_nat(6u);
v___x_3429_ = lean_unsigned_to_nat(108u);
v___x_3430_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3431_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3432_ = l_mkPanicMessageWithDecl(v___x_3431_, v___x_3430_, v___x_3429_, v___x_3428_, v___x_3427_);
return v___x_3432_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
return v___x_3435_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
return v___x_3438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
return v___x_3443_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11(void){
_start:
{
lean_object* v_cellCount_3444_; lean_object* v___x_3445_; 
v_cellCount_3444_ = lean_unsigned_to_nat(16u);
v___x_3445_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3444_);
return v___x_3445_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12(void){
_start:
{
lean_object* v_cellCount_3446_; lean_object* v___x_3447_; 
v_cellCount_3446_ = lean_unsigned_to_nat(16u);
v___x_3447_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3446_);
return v___x_3447_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14(void){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13));
v___x_3450_ = l_Lean_stringToMessageData(v___x_3449_);
return v___x_3450_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15));
v___x_3453_ = l_Lean_stringToMessageData(v___x_3452_);
return v___x_3453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17));
v___x_3456_ = l_Lean_stringToMessageData(v___x_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3464_, lean_object* v_us_3465_, lean_object* v_xs_3466_, lean_object* v___x_3467_, lean_object* v___x_3468_, lean_object* v_ctorName_3469_, lean_object* v___x_3470_, lean_object* v___f_3471_, lean_object* v_insts_3472_, lean_object* v_localInst2Index_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___x_3481_; lean_object* v_env_3482_; lean_object* v___x_3483_; lean_object* v_type_3484_; lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; uint8_t v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v_val_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3654_; lean_object* v___y_3665_; uint8_t v___x_3675_; uint8_t v___x_3676_; 
v___x_3481_ = lean_st_ref_get(v___y_3479_);
v_env_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc_ref(v_env_3482_);
lean_dec(v___x_3481_);
lean_inc(v_us_3465_);
lean_inc(v_inductiveTypeName_3464_);
v___x_3483_ = l_Lean_Expr_const___override(v_inductiveTypeName_3464_, v_us_3465_);
v_type_3484_ = l_Lean_mkAppN(v___x_3483_, v_xs_3466_);
v___x_3675_ = l_Lean_isStructure(v_env_3482_, v_inductiveTypeName_3464_);
v___x_3676_ = 1;
if (v___x_3675_ == 0)
{
lean_object* v_options_3677_; lean_object* v_inheritedTraceOptions_3678_; uint8_t v_hasTrace_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec_ref(v___f_3471_);
v_options_3677_ = lean_ctor_get(v___y_3478_, 2);
v_inheritedTraceOptions_3678_ = lean_ctor_get(v___y_3478_, 13);
v_hasTrace_3679_ = lean_ctor_get_uint8(v_options_3677_, sizeof(void*)*1);
lean_inc(v_ctorName_3469_);
v___x_3680_ = l_Lean_Expr_const___override(v_ctorName_3469_, v_us_3465_);
v___x_3681_ = l_Lean_mkAppN(v___x_3680_, v___x_3470_);
if (v_hasTrace_3679_ == 0)
{
lean_object* v___x_3682_; 
lean_dec(v_ctorName_3469_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc_ref(v___x_3681_);
v___x_3682_ = lean_infer_type(v___x_3681_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; lean_object* v___x_3686_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3684_ = lean_box(0);
v___x_3685_ = 0;
v___x_3686_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3683_, v___x_3684_, v___x_3685_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v_snd_3688_; lean_object* v_fst_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3732_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v_snd_3688_ = lean_ctor_get(v_a_3687_, 1);
v_fst_3689_ = lean_ctor_get(v_a_3687_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_a_3687_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3691_ = v_a_3687_;
v_isShared_3692_ = v_isSharedCheck_3732_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_snd_3688_);
lean_inc(v_fst_3689_);
lean_dec(v_a_3687_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3732_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_snd_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3730_; 
v_snd_3693_ = lean_ctor_get(v_snd_3688_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_snd_3688_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v_snd_3688_, 0);
lean_dec(v_unused_3731_);
v___x_3695_ = v_snd_3688_;
v_isShared_3696_ = v_isSharedCheck_3730_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_snd_3693_);
lean_dec(v_snd_3688_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3730_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; 
lean_inc(v_snd_3693_);
lean_inc_ref(v_type_3484_);
v___x_3697_ = l_Lean_Meta_isExprDefEq(v_type_3484_, v_snd_3693_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; uint8_t v___x_3699_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3697_, 1);
v___x_3699_ = lean_unbox(v_a_3698_);
lean_dec(v_a_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
lean_dec(v_fst_3689_);
lean_dec_ref(v___x_3681_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v___x_3700_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
v___x_3701_ = l_Lean_indentExpr(v_type_3484_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set_tag(v___x_3695_, 7);
lean_ctor_set(v___x_3695_, 1, v___x_3701_);
lean_ctor_set(v___x_3695_, 0, v___x_3700_);
v___x_3703_ = v___x_3695_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18);
if (v_isShared_3692_ == 0)
{
lean_ctor_set_tag(v___x_3691_, 7);
lean_ctor_set(v___x_3691_, 1, v___x_3704_);
lean_ctor_set(v___x_3691_, 0, v___x_3703_);
v___x_3706_ = v___x_3691_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
v___x_3707_ = l_Lean_indentExpr(v_snd_3693_);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3708_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3709_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
lean_del_object(v___x_3695_);
lean_dec(v_snd_3693_);
lean_del_object(v___x_3691_);
v___x_3720_ = lean_box(0);
v___x_3721_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3681_, v_fst_3689_, v___x_3720_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v_fst_3689_);
v___y_3654_ = v___x_3721_;
goto v___jp_3653_;
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_del_object(v___x_3695_);
lean_dec(v_snd_3693_);
lean_del_object(v___x_3691_);
lean_dec(v_fst_3689_);
lean_dec_ref(v___x_3681_);
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v_a_3722_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3697_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3697_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v___x_3681_);
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v_a_3733_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3686_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3686_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
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
else
{
lean_dec_ref(v___x_3681_);
v___y_3654_ = v___x_3682_;
goto v___jp_3653_;
}
}
else
{
lean_object* v___x_3741_; lean_object* v___f_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v_a_3750_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_a_3765_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v_a_3783_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v_a_3795_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; 
v___x_3741_ = lean_box(v___x_3675_);
v___f_3742_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3742_, 0, v_ctorName_3469_);
lean_closure_set(v___f_3742_, 1, v___x_3741_);
v___x_3743_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3744_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3745_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3678_, v_options_3677_, v___x_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = l_Lean_trace_profiler;
v___x_3894_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3677_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
lean_dec_ref(v___f_3742_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc_ref(v___x_3681_);
v___x_3895_ = lean_infer_type(v___x_3681_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; lean_object* v___x_3899_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3895_, 1);
v___x_3897_ = lean_box(0);
v___x_3898_ = 0;
v___x_3899_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3896_, v___x_3897_, v___x_3898_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v_snd_3901_; lean_object* v_fst_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3945_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v_snd_3901_ = lean_ctor_get(v_a_3900_, 1);
v_fst_3902_ = lean_ctor_get(v_a_3900_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v_a_3900_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3904_ = v_a_3900_;
v_isShared_3905_ = v_isSharedCheck_3945_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_snd_3901_);
lean_inc(v_fst_3902_);
lean_dec(v_a_3900_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3945_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v_snd_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3943_; 
v_snd_3906_ = lean_ctor_get(v_snd_3901_, 1);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_snd_3901_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; 
v_unused_3944_ = lean_ctor_get(v_snd_3901_, 0);
lean_dec(v_unused_3944_);
v___x_3908_ = v_snd_3901_;
v_isShared_3909_ = v_isSharedCheck_3943_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_snd_3906_);
lean_dec(v_snd_3901_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3943_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; 
lean_inc(v_snd_3906_);
lean_inc_ref(v_type_3484_);
v___x_3910_ = l_Lean_Meta_isExprDefEq(v_type_3484_, v_snd_3906_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; uint8_t v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = lean_unbox(v_a_3911_);
lean_dec(v_a_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
lean_dec(v_fst_3902_);
lean_dec_ref(v___x_3681_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v___x_3913_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
v___x_3914_ = l_Lean_indentExpr(v_type_3484_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set_tag(v___x_3908_, 7);
lean_ctor_set(v___x_3908_, 1, v___x_3914_);
lean_ctor_set(v___x_3908_, 0, v___x_3913_);
v___x_3916_ = v___x_3908_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18);
if (v_isShared_3905_ == 0)
{
lean_ctor_set_tag(v___x_3904_, 7);
lean_ctor_set(v___x_3904_, 1, v___x_3917_);
lean_ctor_set(v___x_3904_, 0, v___x_3916_);
v___x_3919_ = v___x_3904_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v___x_3920_ = l_Lean_indentExpr(v_snd_3906_);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3921_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3922_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3922_);
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
lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_del_object(v___x_3908_);
lean_dec(v_snd_3906_);
lean_del_object(v___x_3904_);
v___x_3933_ = lean_box(0);
v___x_3934_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3681_, v_fst_3902_, v___x_3933_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v_fst_3902_);
v___y_3654_ = v___x_3934_;
goto v___jp_3653_;
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_del_object(v___x_3908_);
lean_dec(v_snd_3906_);
lean_del_object(v___x_3904_);
lean_dec(v_fst_3902_);
lean_dec_ref(v___x_3681_);
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v_a_3935_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3910_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3910_);
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
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v___x_3681_);
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v_a_3946_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3899_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3899_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
else
{
lean_dec_ref(v___x_3681_);
v___y_3654_ = v___x_3895_;
goto v___jp_3653_;
}
}
else
{
goto v___jp_3810_;
}
}
else
{
goto v___jp_3810_;
}
v___jp_3747_:
{
lean_object* v___x_3751_; double v___x_3752_; double v___x_3753_; double v___x_3754_; double v___x_3755_; double v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3751_ = lean_io_mono_nanos_now();
v___x_3752_ = lean_float_of_nat(v___y_3749_);
v___x_3753_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3754_ = lean_float_div(v___x_3752_, v___x_3753_);
v___x_3755_ = lean_float_of_nat(v___x_3751_);
v___x_3756_ = lean_float_div(v___x_3755_, v___x_3753_);
v___x_3757_ = lean_box_float(v___x_3754_);
v___x_3758_ = lean_box_float(v___x_3756_);
v___x_3759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v_a_3750_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3743_, v___x_3676_, v___x_3744_, v_options_3677_, v___x_3746_, v___y_3748_, v___f_3742_, v___x_3760_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3654_ = v___x_3761_;
goto v___jp_3653_;
}
v___jp_3762_:
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v_a_3765_);
v___y_3748_ = v___y_3763_;
v___y_3749_ = v___y_3764_;
v_a_3750_ = v___x_3766_;
goto v___jp_3747_;
}
v___jp_3767_:
{
if (lean_obj_tag(v___y_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
v_a_3771_ = lean_ctor_get(v___y_3770_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___y_3770_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___y_3770_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___y_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
lean_ctor_set_tag(v___x_3773_, 1);
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
v___y_3748_ = v___y_3768_;
v___y_3749_ = v___y_3769_;
v_a_3750_ = v___x_3776_;
goto v___jp_3747_;
}
}
}
else
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___y_3770_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___y_3770_, 1);
v___y_3763_ = v___y_3768_;
v___y_3764_ = v___y_3769_;
v_a_3765_ = v_a_3779_;
goto v___jp_3762_;
}
}
v___jp_3780_:
{
lean_object* v___x_3784_; double v___x_3785_; double v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3784_ = lean_io_get_num_heartbeats();
v___x_3785_ = lean_float_of_nat(v___y_3781_);
v___x_3786_ = lean_float_of_nat(v___x_3784_);
v___x_3787_ = lean_box_float(v___x_3785_);
v___x_3788_ = lean_box_float(v___x_3786_);
v___x_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v_a_3783_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3743_, v___x_3676_, v___x_3744_, v_options_3677_, v___x_3746_, v___y_3782_, v___f_3742_, v___x_3790_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3654_ = v___x_3791_;
goto v___jp_3653_;
}
v___jp_3792_:
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_a_3795_);
v___y_3781_ = v___y_3793_;
v___y_3782_ = v___y_3794_;
v_a_3783_ = v___x_3796_;
goto v___jp_3780_;
}
v___jp_3797_:
{
if (lean_obj_tag(v___y_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
v_a_3801_ = lean_ctor_get(v___y_3800_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___y_3800_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___y_3800_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___y_3800_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 1);
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
v___y_3781_ = v___y_3798_;
v___y_3782_ = v___y_3799_;
v_a_3783_ = v___x_3806_;
goto v___jp_3780_;
}
}
}
else
{
lean_object* v_a_3809_; 
v_a_3809_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v___y_3800_, 1);
v___y_3793_ = v___y_3798_;
v___y_3794_ = v___y_3799_;
v_a_3795_ = v_a_3809_;
goto v___jp_3792_;
}
}
v___jp_3810_:
{
lean_object* v___x_3811_; lean_object* v_a_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3811_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3479_);
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref(v___x_3811_);
v___x_3813_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3814_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3677_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = lean_io_mono_nanos_now();
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc_ref(v___x_3681_);
v___x_3816_ = lean_infer_type(v___x_3681_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = lean_box(0);
v___x_3819_ = 0;
v___x_3820_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3817_, v___x_3818_, v___x_3819_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v_snd_3822_; lean_object* v_fst_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3852_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v_snd_3822_ = lean_ctor_get(v_a_3821_, 1);
v_fst_3823_ = lean_ctor_get(v_a_3821_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_a_3821_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3825_ = v_a_3821_;
v_isShared_3826_ = v_isSharedCheck_3852_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_snd_3822_);
lean_inc(v_fst_3823_);
lean_dec(v_a_3821_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3852_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v_snd_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3850_; 
v_snd_3827_ = lean_ctor_get(v_snd_3822_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_snd_3822_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v_snd_3822_, 0);
lean_dec(v_unused_3851_);
v___x_3829_ = v_snd_3822_;
v_isShared_3830_ = v_isSharedCheck_3850_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_snd_3827_);
lean_dec(v_snd_3822_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3850_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; 
lean_inc(v_snd_3827_);
lean_inc_ref(v_type_3484_);
v___x_3831_ = l_Lean_Meta_isExprDefEq(v_type_3484_, v_snd_3827_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; uint8_t v___x_3833_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
v___x_3833_ = lean_unbox(v_a_3832_);
lean_dec(v_a_3832_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3837_; 
lean_dec(v_fst_3823_);
lean_dec_ref(v___x_3681_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
lean_inc_ref(v_type_3484_);
v___x_3835_ = l_Lean_indentExpr(v_type_3484_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set_tag(v___x_3829_, 7);
lean_ctor_set(v___x_3829_, 1, v___x_3835_);
lean_ctor_set(v___x_3829_, 0, v___x_3834_);
v___x_3837_ = v___x_3829_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3838_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18);
if (v_isShared_3826_ == 0)
{
lean_ctor_set_tag(v___x_3825_, 7);
lean_ctor_set(v___x_3825_, 1, v___x_3838_);
lean_ctor_set(v___x_3825_, 0, v___x_3837_);
v___x_3840_ = v___x_3825_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v_a_3844_; 
v___x_3841_ = l_Lean_indentExpr(v_snd_3827_);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3842_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___x_3843_);
v___y_3763_ = v_a_3812_;
v___y_3764_ = v___x_3815_;
v_a_3765_ = v_a_3844_;
goto v___jp_3762_;
}
}
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_del_object(v___x_3829_);
lean_dec(v_snd_3827_);
lean_del_object(v___x_3825_);
v___x_3847_ = lean_box(0);
v___x_3848_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3681_, v_fst_3823_, v___x_3847_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v_fst_3823_);
v___y_3768_ = v_a_3812_;
v___y_3769_ = v___x_3815_;
v___y_3770_ = v___x_3848_;
goto v___jp_3767_;
}
}
else
{
lean_object* v_a_3849_; 
lean_del_object(v___x_3829_);
lean_dec(v_snd_3827_);
lean_del_object(v___x_3825_);
lean_dec(v_fst_3823_);
lean_dec_ref(v___x_3681_);
v_a_3849_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3831_, 1);
v___y_3763_ = v_a_3812_;
v___y_3764_ = v___x_3815_;
v_a_3765_ = v_a_3849_;
goto v___jp_3762_;
}
}
}
}
else
{
lean_object* v_a_3853_; 
lean_dec_ref(v___x_3681_);
v_a_3853_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3820_, 1);
v___y_3763_ = v_a_3812_;
v___y_3764_ = v___x_3815_;
v_a_3765_ = v_a_3853_;
goto v___jp_3762_;
}
}
else
{
lean_dec_ref(v___x_3681_);
v___y_3768_ = v_a_3812_;
v___y_3769_ = v___x_3815_;
v___y_3770_ = v___x_3816_;
goto v___jp_3767_;
}
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc_ref(v___x_3681_);
v___x_3855_ = lean_infer_type(v___x_3681_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; lean_object* v___x_3859_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___x_3857_ = lean_box(0);
v___x_3858_ = 0;
v___x_3859_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3856_, v___x_3857_, v___x_3858_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v_snd_3861_; lean_object* v_fst_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3891_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3859_, 1);
v_snd_3861_ = lean_ctor_get(v_a_3860_, 1);
v_fst_3862_ = lean_ctor_get(v_a_3860_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_a_3860_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3864_ = v_a_3860_;
v_isShared_3865_ = v_isSharedCheck_3891_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_snd_3861_);
lean_inc(v_fst_3862_);
lean_dec(v_a_3860_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3891_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v_snd_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3889_; 
v_snd_3866_ = lean_ctor_get(v_snd_3861_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_snd_3861_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v_snd_3861_, 0);
lean_dec(v_unused_3890_);
v___x_3868_ = v_snd_3861_;
v_isShared_3869_ = v_isSharedCheck_3889_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_snd_3866_);
lean_dec(v_snd_3861_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3889_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; 
lean_inc(v_snd_3866_);
lean_inc_ref(v_type_3484_);
v___x_3870_ = l_Lean_Meta_isExprDefEq(v_type_3484_, v_snd_3866_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; uint8_t v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___x_3872_ = lean_unbox(v_a_3871_);
lean_dec(v_a_3871_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
lean_dec(v_fst_3862_);
lean_dec_ref(v___x_3681_);
v___x_3873_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
lean_inc_ref(v_type_3484_);
v___x_3874_ = l_Lean_indentExpr(v_type_3484_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 7);
lean_ctor_set(v___x_3868_, 1, v___x_3874_);
lean_ctor_set(v___x_3868_, 0, v___x_3873_);
v___x_3876_ = v___x_3868_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3873_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3877_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18);
if (v_isShared_3865_ == 0)
{
lean_ctor_set_tag(v___x_3864_, 7);
lean_ctor_set(v___x_3864_, 1, v___x_3877_);
lean_ctor_set(v___x_3864_, 0, v___x_3876_);
v___x_3879_ = v___x_3864_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; 
v___x_3880_ = l_Lean_indentExpr(v_snd_3866_);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3881_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v___x_3882_);
v___y_3793_ = v___x_3854_;
v___y_3794_ = v_a_3812_;
v_a_3795_ = v_a_3883_;
goto v___jp_3792_;
}
}
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
lean_del_object(v___x_3868_);
lean_dec(v_snd_3866_);
lean_del_object(v___x_3864_);
v___x_3886_ = lean_box(0);
v___x_3887_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3681_, v_fst_3862_, v___x_3886_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v_fst_3862_);
v___y_3798_ = v___x_3854_;
v___y_3799_ = v_a_3812_;
v___y_3800_ = v___x_3887_;
goto v___jp_3797_;
}
}
else
{
lean_object* v_a_3888_; 
lean_del_object(v___x_3868_);
lean_dec(v_snd_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_fst_3862_);
lean_dec_ref(v___x_3681_);
v_a_3888_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3793_ = v___x_3854_;
v___y_3794_ = v_a_3812_;
v_a_3795_ = v_a_3888_;
goto v___jp_3792_;
}
}
}
}
else
{
lean_object* v_a_3892_; 
lean_dec_ref(v___x_3681_);
v_a_3892_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3859_, 1);
v___y_3793_ = v___x_3854_;
v___y_3794_ = v_a_3812_;
v_a_3795_ = v_a_3892_;
goto v___jp_3792_;
}
}
else
{
lean_dec_ref(v___x_3681_);
v___y_3798_ = v___x_3854_;
v___y_3799_ = v_a_3812_;
v___y_3800_ = v___x_3855_;
goto v___jp_3797_;
}
}
}
}
}
else
{
lean_object* v_options_3954_; uint8_t v_hasTrace_3955_; 
lean_dec(v_ctorName_3469_);
lean_dec(v_us_3465_);
v_options_3954_ = lean_ctor_get(v___y_3478_, 2);
v_hasTrace_3955_ = lean_ctor_get_uint8(v_options_3954_, sizeof(void*)*1);
if (v_hasTrace_3955_ == 0)
{
lean_object* v_ref_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec_ref(v___f_3471_);
v_ref_3956_ = lean_ctor_get(v___y_3478_, 5);
v___x_3957_ = l_Lean_SourceInfo_fromRef(v_ref_3956_, v_hasTrace_3955_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
v___x_3959_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc(v___x_3957_);
v___x_3960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3957_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = l_Lean_Syntax_node1(v___x_3957_, v___x_3958_, v___x_3960_);
lean_inc_ref(v_type_3484_);
v___x_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3962_, 0, v_type_3484_);
v___x_3963_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3963_, 0, v___x_3961_);
lean_closure_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3963_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3665_ = v___x_3964_;
goto v___jp_3664_;
}
else
{
lean_object* v_ref_3965_; lean_object* v_inheritedTraceOptions_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v_a_3974_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v_a_3989_; 
v_ref_3965_ = lean_ctor_get(v___y_3478_, 5);
v_inheritedTraceOptions_3966_ = lean_ctor_get(v___y_3478_, 13);
v___x_3967_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3968_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3969_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3970_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3966_, v_options_3954_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_4062_; uint8_t v___x_4063_; 
v___x_4062_ = l_Lean_trace_profiler;
v___x_4063_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3954_, v___x_4062_);
if (v___x_4063_ == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec_ref(v___f_3471_);
v___x_4064_ = l_Lean_SourceInfo_fromRef(v_ref_3965_, v___x_4063_);
v___x_4065_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
v___x_4066_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc(v___x_4064_);
v___x_4067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4064_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = l_Lean_Syntax_node1(v___x_4064_, v___x_4065_, v___x_4067_);
lean_inc_ref(v_type_3484_);
v___x_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4069_, 0, v_type_3484_);
v___x_4070_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_4070_, 0, v___x_4068_);
lean_closure_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_4070_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3665_ = v___x_4071_;
goto v___jp_3664_;
}
else
{
goto v___jp_3998_;
}
}
else
{
goto v___jp_3998_;
}
v___jp_3971_:
{
lean_object* v___x_3975_; double v___x_3976_; double v___x_3977_; double v___x_3978_; double v___x_3979_; double v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3975_ = lean_io_mono_nanos_now();
v___x_3976_ = lean_float_of_nat(v___y_3972_);
v___x_3977_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3978_ = lean_float_div(v___x_3976_, v___x_3977_);
v___x_3979_ = lean_float_of_nat(v___x_3975_);
v___x_3980_ = lean_float_div(v___x_3979_, v___x_3977_);
v___x_3981_ = lean_box_float(v___x_3978_);
v___x_3982_ = lean_box_float(v___x_3980_);
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3981_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v_a_3974_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3967_, v___x_3676_, v___x_3968_, v_options_3954_, v___x_3970_, v___y_3973_, v___f_3471_, v___x_3984_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3665_ = v___x_3985_;
goto v___jp_3664_;
}
v___jp_3986_:
{
lean_object* v___x_3990_; double v___x_3991_; double v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3990_ = lean_io_get_num_heartbeats();
v___x_3991_ = lean_float_of_nat(v___y_3987_);
v___x_3992_ = lean_float_of_nat(v___x_3990_);
v___x_3993_ = lean_box_float(v___x_3991_);
v___x_3994_ = lean_box_float(v___x_3992_);
v___x_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3993_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v_a_3989_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3967_, v___x_3676_, v___x_3968_, v_options_3954_, v___x_3970_, v___y_3988_, v___f_3471_, v___x_3996_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3665_ = v___x_3997_;
goto v___jp_3664_;
}
v___jp_3998_:
{
lean_object* v___x_3999_; lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4061_; 
v___x_3999_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3479_);
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4061_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4061_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4004_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4005_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3954_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4006_ = lean_io_mono_nanos_now();
v___x_4007_ = l_Lean_SourceInfo_fromRef(v_ref_3965_, v___x_4005_);
v___x_4008_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
v___x_4009_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc(v___x_4007_);
v___x_4010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4007_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
v___x_4011_ = l_Lean_Syntax_node1(v___x_4007_, v___x_4008_, v___x_4010_);
lean_inc_ref(v_type_3484_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set_tag(v___x_4002_, 1);
lean_ctor_set(v___x_4002_, 0, v_type_3484_);
v___x_4013_ = v___x_4002_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_type_3484_);
v___x_4013_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_4014_, 0, v___x_4011_);
lean_closure_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_4014_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4015_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set_tag(v___x_4018_, 1);
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
v___y_3972_ = v___x_4006_;
v___y_3973_ = v_a_4000_;
v_a_3974_ = v___x_4021_;
goto v___jp_3971_;
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
v_a_4024_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4015_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4015_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set_tag(v___x_4026_, 0);
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
v___y_3972_ = v___x_4006_;
v___y_3973_ = v_a_4000_;
v_a_3974_ = v___x_4029_;
goto v___jp_3971_;
}
}
}
}
}
else
{
lean_object* v___x_4033_; uint8_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4033_ = lean_io_get_num_heartbeats();
v___x_4034_ = 0;
v___x_4035_ = l_Lean_SourceInfo_fromRef(v_ref_3965_, v___x_4034_);
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
v___x_4037_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc(v___x_4035_);
v___x_4038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4035_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = l_Lean_Syntax_node1(v___x_4035_, v___x_4036_, v___x_4038_);
lean_inc_ref(v_type_3484_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set_tag(v___x_4002_, 1);
lean_ctor_set(v___x_4002_, 0, v_type_3484_);
v___x_4041_ = v___x_4002_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_type_3484_);
v___x_4041_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_4042_, 0, v___x_4039_);
lean_closure_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_4042_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4043_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4043_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 1);
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
v___y_3987_ = v___x_4033_;
v___y_3988_ = v_a_4000_;
v_a_3989_ = v___x_4049_;
goto v___jp_3986_;
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
v_a_4052_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4043_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4043_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set_tag(v___x_4054_, 0);
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
v___y_3987_ = v___x_4033_;
v___y_3988_ = v_a_4000_;
v_a_3989_ = v___x_4057_;
goto v___jp_3986_;
}
}
}
}
}
}
}
}
}
v___jp_3485_:
{
lean_object* v___x_3494_; uint8_t v___x_3495_; uint8_t v___x_3496_; lean_object* v___x_3497_; 
v___x_3494_ = l_Array_append___redArg(v_xs_3466_, v___y_3489_);
lean_dec_ref(v___y_3489_);
v___x_3495_ = 0;
v___x_3496_ = 1;
v___x_3497_ = l_Lean_Meta_mkForallFVars(v___x_3494_, v_type_3484_, v___x_3495_, v___y_3488_, v___y_3488_, v___x_3496_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = l_Lean_Meta_mkLambdaFVars(v___x_3494_, v___y_3487_, v___x_3495_, v___y_3488_, v___x_3495_, v___y_3488_, v___x_3496_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec_ref(v___x_3494_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3509_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3509_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3509_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v_a_3500_);
lean_ctor_set(v___x_3504_, 1, v___y_3486_);
v___x_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3505_, 0, v_a_3498_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3505_);
v___x_3507_ = v___x_3502_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec(v_a_3498_);
lean_dec(v___y_3486_);
v_a_3510_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3499_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3499_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___x_3494_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
v_a_3518_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3497_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3497_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
v___jp_3526_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___y_3528_);
lean_ctor_set(v___x_3538_, 1, v___y_3537_);
lean_inc(v___y_3536_);
v___x_3539_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3536_, v___x_3538_, v___y_3534_, v___y_3531_, v___y_3532_, v___y_3535_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_dec_ref_known(v___x_3539_, 1);
v___y_3486_ = v___y_3527_;
v___y_3487_ = v___y_3529_;
v___y_3488_ = v___y_3530_;
v___y_3489_ = v___y_3533_;
v___y_3490_ = v___y_3534_;
v___y_3491_ = v___y_3531_;
v___y_3492_ = v___y_3532_;
v___y_3493_ = v___y_3535_;
goto v___jp_3485_;
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3527_);
lean_dec_ref(v_type_3484_);
lean_dec_ref(v_xs_3466_);
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
v___jp_3548_:
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_nat_dec_eq(v___y_3557_, v___y_3559_);
lean_dec(v___y_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v_type_3484_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v___x_3561_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3562_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3561_, v___y_3552_, v___y_3551_, v___y_3556_, v___y_3553_, v___y_3554_, v___y_3558_);
return v___x_3562_;
}
else
{
lean_object* v_options_3563_; uint8_t v_hasTrace_3564_; 
v_options_3563_ = lean_ctor_get(v___y_3554_, 2);
v_hasTrace_3564_ = lean_ctor_get_uint8(v_options_3563_, sizeof(void*)*1);
if (v_hasTrace_3564_ == 0)
{
lean_dec(v___y_3557_);
lean_dec(v___x_3467_);
v___y_3486_ = v___y_3549_;
v___y_3487_ = v___y_3550_;
v___y_3488_ = v___x_3560_;
v___y_3489_ = v___y_3555_;
v___y_3490_ = v___y_3556_;
v___y_3491_ = v___y_3553_;
v___y_3492_ = v___y_3554_;
v___y_3493_ = v___y_3558_;
goto v___jp_3485_;
}
else
{
lean_object* v_inheritedTraceOptions_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v_inheritedTraceOptions_3565_ = lean_ctor_get(v___y_3554_, 13);
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3567_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3565_, v_options_3563_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_dec(v___y_3557_);
lean_dec(v___x_3467_);
v___y_3486_ = v___y_3549_;
v___y_3487_ = v___y_3550_;
v___y_3488_ = v___x_3560_;
v___y_3489_ = v___y_3555_;
v___y_3490_ = v___y_3556_;
v___y_3491_ = v___y_3553_;
v___y_3492_ = v___y_3554_;
v___y_3493_ = v___y_3558_;
goto v___jp_3485_;
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v___x_3569_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3570_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3550_);
v___x_3571_ = l_Lean_inlineExpr(v___y_3550_, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3569_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = lean_nat_dec_eq(v___y_3557_, v___x_3467_);
lean_dec(v___x_3467_);
lean_dec(v___y_3557_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3574_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3555_);
v___x_3575_ = lean_array_to_list(v___y_3555_);
v___x_3576_ = lean_box(0);
v___x_3577_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3575_, v___x_3576_);
v___x_3578_ = l_Lean_MessageData_ofList(v___x_3577_);
v___x_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3574_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___y_3527_ = v___y_3549_;
v___y_3528_ = v___x_3572_;
v___y_3529_ = v___y_3550_;
v___y_3530_ = v___x_3560_;
v___y_3531_ = v___y_3553_;
v___y_3532_ = v___y_3554_;
v___y_3533_ = v___y_3555_;
v___y_3534_ = v___y_3556_;
v___y_3535_ = v___y_3558_;
v___y_3536_ = v___x_3566_;
v___y_3537_ = v___x_3581_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3582_; 
v___x_3582_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3527_ = v___y_3549_;
v___y_3528_ = v___x_3572_;
v___y_3529_ = v___y_3550_;
v___y_3530_ = v___x_3560_;
v___y_3531_ = v___y_3553_;
v___y_3532_ = v___y_3554_;
v___y_3533_ = v___y_3555_;
v___y_3534_ = v___y_3556_;
v___y_3535_ = v___y_3558_;
v___y_3536_ = v___x_3566_;
v___y_3537_ = v___x_3582_;
goto v___jp_3526_;
}
}
}
}
}
v___jp_3583_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = lean_box(1);
lean_inc_ref(v___y_3584_);
v___x_3593_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3592_, v_localInst2Index_3473_, v___y_3584_);
v___x_3594_ = lean_array_get_size(v___y_3591_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_size_3595_; 
v_size_3595_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_size_3595_);
v___y_3549_ = v___x_3593_;
v___y_3550_ = v___y_3584_;
v___y_3551_ = v___y_3585_;
v___y_3552_ = v___y_3586_;
v___y_3553_ = v___y_3587_;
v___y_3554_ = v___y_3588_;
v___y_3555_ = v___y_3591_;
v___y_3556_ = v___y_3589_;
v___y_3557_ = v___x_3594_;
v___y_3558_ = v___y_3590_;
v___y_3559_ = v_size_3595_;
goto v___jp_3548_;
}
else
{
lean_inc(v___x_3467_);
v___y_3549_ = v___x_3593_;
v___y_3550_ = v___y_3584_;
v___y_3551_ = v___y_3585_;
v___y_3552_ = v___y_3586_;
v___y_3553_ = v___y_3587_;
v___y_3554_ = v___y_3588_;
v___y_3555_ = v___y_3591_;
v___y_3556_ = v___y_3589_;
v___y_3557_ = v___x_3594_;
v___y_3558_ = v___y_3590_;
v___y_3559_ = v___x_3467_;
goto v___jp_3548_;
}
}
v___jp_3596_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3604_ = lean_array_get_size(v_insts_3472_);
v___x_3605_ = lean_mk_empty_array_with_capacity(v___x_3467_);
v___x_3606_ = lean_nat_dec_lt(v___x_3467_, v___x_3604_);
if (v___x_3606_ == 0)
{
lean_dec(v___x_3468_);
v___y_3584_ = v___y_3597_;
v___y_3585_ = v___y_3599_;
v___y_3586_ = v___y_3598_;
v___y_3587_ = v___y_3601_;
v___y_3588_ = v___y_3602_;
v___y_3589_ = v___y_3600_;
v___y_3590_ = v___y_3603_;
v___y_3591_ = v___x_3605_;
goto v___jp_3583_;
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v_visitedExpr_3612_; uint8_t v___x_3613_; 
v___x_3607_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
v___x_3608_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12);
lean_inc(v___x_3467_);
v___x_3609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3467_);
lean_ctor_set(v___x_3609_, 1, v___x_3607_);
lean_ctor_set(v___x_3609_, 2, v___x_3608_);
lean_inc_ref(v___x_3605_);
v___x_3610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v___x_3468_);
lean_ctor_set(v___x_3610_, 2, v___x_3605_);
lean_inc_ref(v___y_3597_);
v___x_3611_ = l_Lean_collectFVars(v___x_3610_, v___y_3597_);
v_visitedExpr_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc_ref(v_visitedExpr_3612_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = lean_nat_dec_le(v___x_3604_, v___x_3604_);
if (v___x_3613_ == 0)
{
if (v___x_3606_ == 0)
{
lean_dec_ref(v_visitedExpr_3612_);
v___y_3584_ = v___y_3597_;
v___y_3585_ = v___y_3599_;
v___y_3586_ = v___y_3598_;
v___y_3587_ = v___y_3601_;
v___y_3588_ = v___y_3602_;
v___y_3589_ = v___y_3600_;
v___y_3590_ = v___y_3603_;
v___y_3591_ = v___x_3605_;
goto v___jp_3583_;
}
else
{
size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = lean_usize_of_nat(v___x_3604_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3612_, v_insts_3472_, v___x_3614_, v___x_3615_, v___x_3605_);
lean_dec_ref(v_visitedExpr_3612_);
v___y_3584_ = v___y_3597_;
v___y_3585_ = v___y_3599_;
v___y_3586_ = v___y_3598_;
v___y_3587_ = v___y_3601_;
v___y_3588_ = v___y_3602_;
v___y_3589_ = v___y_3600_;
v___y_3590_ = v___y_3603_;
v___y_3591_ = v___x_3616_;
goto v___jp_3583_;
}
}
else
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = lean_usize_of_nat(v___x_3604_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3612_, v_insts_3472_, v___x_3617_, v___x_3618_, v___x_3605_);
lean_dec_ref(v_visitedExpr_3612_);
v___y_3584_ = v___y_3597_;
v___y_3585_ = v___y_3599_;
v___y_3586_ = v___y_3598_;
v___y_3587_ = v___y_3601_;
v___y_3588_ = v___y_3602_;
v___y_3589_ = v___y_3600_;
v___y_3590_ = v___y_3603_;
v___y_3591_ = v___x_3619_;
goto v___jp_3583_;
}
}
}
v___jp_3620_:
{
lean_object* v___x_3628_; 
lean_inc_ref(v_val_3621_);
v___x_3628_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; lean_object* v_a_3630_; uint8_t v___x_3631_; 
lean_dec_ref_known(v___x_3628_, 1);
v___x_3629_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3621_, v___y_3625_);
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3629_);
v___x_3631_ = l_Lean_Expr_hasMVar(v_a_3630_);
if (v___x_3631_ == 0)
{
v___y_3597_ = v_a_3630_;
v___y_3598_ = v___y_3622_;
v___y_3599_ = v___y_3623_;
v___y_3600_ = v___y_3624_;
v___y_3601_ = v___y_3625_;
v___y_3602_ = v___y_3626_;
v___y_3603_ = v___y_3627_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v___x_3632_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14);
v___x_3633_ = lean_unsigned_to_nat(30u);
v___x_3634_ = l_Lean_inlineExprTrailing(v_a_3630_, v___x_3633_);
v___x_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3632_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3635_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec_ref(v_val_3621_);
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v_a_3645_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3628_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3628_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
v___jp_3653_:
{
if (lean_obj_tag(v___y_3654_) == 0)
{
lean_object* v_a_3655_; 
v_a_3655_ = lean_ctor_get(v___y_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___y_3654_, 1);
v_val_3621_ = v_a_3655_;
v___y_3622_ = v___y_3474_;
v___y_3623_ = v___y_3475_;
v___y_3624_ = v___y_3476_;
v___y_3625_ = v___y_3477_;
v___y_3626_ = v___y_3478_;
v___y_3627_ = v___y_3479_;
goto v___jp_3620_;
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v_a_3656_ = lean_ctor_get(v___y_3654_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___y_3654_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___y_3654_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___y_3654_);
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
v___jp_3664_:
{
if (lean_obj_tag(v___y_3665_) == 0)
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v___y_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___y_3665_, 1);
v_val_3621_ = v_a_3666_;
v___y_3622_ = v___y_3474_;
v___y_3623_ = v___y_3475_;
v___y_3624_ = v___y_3476_;
v___y_3625_ = v___y_3477_;
v___y_3626_ = v___y_3478_;
v___y_3627_ = v___y_3479_;
goto v___jp_3620_;
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec_ref(v_type_3484_);
lean_dec(v_localInst2Index_3473_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3466_);
v_a_3667_ = lean_ctor_get(v___y_3665_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___y_3665_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___y_3665_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___y_3665_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_4072_ = _args[0];
lean_object* v_us_4073_ = _args[1];
lean_object* v_xs_4074_ = _args[2];
lean_object* v___x_4075_ = _args[3];
lean_object* v___x_4076_ = _args[4];
lean_object* v_ctorName_4077_ = _args[5];
lean_object* v___x_4078_ = _args[6];
lean_object* v___f_4079_ = _args[7];
lean_object* v_insts_4080_ = _args[8];
lean_object* v_localInst2Index_4081_ = _args[9];
lean_object* v___y_4082_ = _args[10];
lean_object* v___y_4083_ = _args[11];
lean_object* v___y_4084_ = _args[12];
lean_object* v___y_4085_ = _args[13];
lean_object* v___y_4086_ = _args[14];
lean_object* v___y_4087_ = _args[15];
lean_object* v___y_4088_ = _args[16];
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_4072_, v_us_4073_, v_xs_4074_, v___x_4075_, v___x_4076_, v_ctorName_4077_, v___x_4078_, v___f_4079_, v_insts_4080_, v_localInst2Index_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec_ref(v_insts_4080_);
lean_dec_ref(v___x_4078_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_4090_, size_t v_i_4091_, lean_object* v_bs_4092_){
_start:
{
uint8_t v___x_4093_; 
v___x_4093_ = lean_usize_dec_lt(v_i_4091_, v_sz_4090_);
if (v___x_4093_ == 0)
{
return v_bs_4092_;
}
else
{
lean_object* v_v_4094_; lean_object* v___x_4095_; lean_object* v_bs_x27_4096_; lean_object* v___x_4097_; uint8_t v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; size_t v___x_4101_; size_t v___x_4102_; lean_object* v___x_4103_; 
v_v_4094_ = lean_array_uget(v_bs_4092_, v_i_4091_);
v___x_4095_ = lean_unsigned_to_nat(0u);
v_bs_x27_4096_ = lean_array_uset(v_bs_4092_, v_i_4091_, v___x_4095_);
v___x_4097_ = l_Lean_Expr_fvarId_x21(v_v_4094_);
lean_dec(v_v_4094_);
v___x_4098_ = 1;
v___x_4099_ = lean_box(v___x_4098_);
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4097_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = ((size_t)1ULL);
v___x_4102_ = lean_usize_add(v_i_4091_, v___x_4101_);
v___x_4103_ = lean_array_uset(v_bs_x27_4096_, v_i_4091_, v___x_4100_);
v_i_4091_ = v___x_4102_;
v_bs_4092_ = v___x_4103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_4105_, lean_object* v_i_4106_, lean_object* v_bs_4107_){
_start:
{
size_t v_sz_boxed_4108_; size_t v_i_boxed_4109_; lean_object* v_res_4110_; 
v_sz_boxed_4108_ = lean_unbox_usize(v_sz_4105_);
lean_dec(v_sz_4105_);
v_i_boxed_4109_ = lean_unbox_usize(v_i_4106_);
lean_dec(v_i_4106_);
v_res_4110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_4108_, v_i_boxed_4109_, v_bs_4107_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
v___x_4119_ = lean_apply_7(v_k_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, lean_box(0));
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_4129_, lean_object* v_k_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v___f_4138_; lean_object* v___x_4139_; 
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
v___f_4138_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4138_, 0, v_k_4130_);
lean_closure_set(v___f_4138_, 1, v___y_4131_);
lean_closure_set(v___f_4138_, 2, v___y_4132_);
v___x_4139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_4129_, v___f_4138_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4139_) == 0)
{
return v___x_4139_;
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4139_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4139_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4148_, lean_object* v_k_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4148_, v_k_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v_bs_4148_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4158_, lean_object* v_k_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
size_t v_sz_4167_; size_t v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_sz_4167_ = lean_array_size(v_bs_4158_);
v___x_4168_ = ((size_t)0ULL);
v___x_4169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4167_, v___x_4168_, v_bs_4158_);
v___x_4170_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4169_, v_k_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
lean_dec_ref(v___x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4171_, lean_object* v_k_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4171_, v_k_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4181_, lean_object* v_inductiveTypeName_4182_, lean_object* v_us_4183_, lean_object* v___x_4184_, lean_object* v_ctorName_4185_, lean_object* v___f_4186_, uint8_t v_addHypotheses_4187_, lean_object* v_xs_4188_, lean_object* v_x_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4197_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4188_, 2);
v___x_4198_ = l_Array_toSubarray___redArg(v_xs_4188_, v___x_4197_, v_numParams_4181_);
v___x_4199_ = l_Subarray_copy___redArg(v___x_4198_);
lean_inc_ref(v___x_4199_);
v___f_4200_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4200_, 0, v_inductiveTypeName_4182_);
lean_closure_set(v___f_4200_, 1, v_us_4183_);
lean_closure_set(v___f_4200_, 2, v_xs_4188_);
lean_closure_set(v___f_4200_, 3, v___x_4197_);
lean_closure_set(v___f_4200_, 4, v___x_4184_);
lean_closure_set(v___f_4200_, 5, v_ctorName_4185_);
lean_closure_set(v___f_4200_, 6, v___x_4199_);
lean_closure_set(v___f_4200_, 7, v___f_4186_);
v___x_4201_ = lean_box(v_addHypotheses_4187_);
v___x_4202_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4202_, 0, v___x_4201_);
lean_closure_set(v___x_4202_, 1, lean_box(0));
lean_closure_set(v___x_4202_, 2, v___x_4199_);
lean_closure_set(v___x_4202_, 3, v___f_4200_);
v___x_4203_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4188_, v___x_4202_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4204_, lean_object* v_inductiveTypeName_4205_, lean_object* v_us_4206_, lean_object* v___x_4207_, lean_object* v_ctorName_4208_, lean_object* v___f_4209_, lean_object* v_addHypotheses_4210_, lean_object* v_xs_4211_, lean_object* v_x_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
uint8_t v_addHypotheses_boxed_4220_; lean_object* v_res_4221_; 
v_addHypotheses_boxed_4220_ = lean_unbox(v_addHypotheses_4210_);
v_res_4221_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4204_, v_inductiveTypeName_4205_, v_us_4206_, v___x_4207_, v_ctorName_4208_, v___f_4209_, v_addHypotheses_boxed_4220_, v_xs_4211_, v_x_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec_ref(v_x_4212_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
if (lean_obj_tag(v_a_4222_) == 0)
{
lean_object* v___x_4224_; 
v___x_4224_ = l_List_reverse___redArg(v_a_4223_);
return v___x_4224_;
}
else
{
lean_object* v_head_4225_; lean_object* v_tail_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4235_; 
v_head_4225_ = lean_ctor_get(v_a_4222_, 0);
v_tail_4226_ = lean_ctor_get(v_a_4222_, 1);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_a_4222_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4228_ = v_a_4222_;
v_isShared_4229_ = v_isSharedCheck_4235_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_tail_4226_);
lean_inc(v_head_4225_);
lean_dec(v_a_4222_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4235_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; lean_object* v___x_4232_; 
v___x_4230_ = l_Lean_Level_param___override(v_head_4225_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 1, v_a_4223_);
lean_ctor_set(v___x_4228_, 0, v___x_4230_);
v___x_4232_ = v___x_4228_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4230_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v_a_4223_);
v___x_4232_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
v_a_4222_ = v_tail_4226_;
v_a_4223_ = v___x_4232_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4237_, lean_object* v_ctorName_4238_, uint8_t v_addHypotheses_4239_, lean_object* v_indVal_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v_toConstantVal_4248_; lean_object* v_numParams_4249_; lean_object* v_levelParams_4250_; lean_object* v_type_4251_; lean_object* v___f_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v_us_4255_; lean_object* v___x_4256_; lean_object* v___f_4257_; uint8_t v___x_4258_; lean_object* v___x_4259_; 
v_toConstantVal_4248_ = lean_ctor_get(v_indVal_4240_, 0);
lean_inc_ref(v_toConstantVal_4248_);
v_numParams_4249_ = lean_ctor_get(v_indVal_4240_, 1);
lean_inc(v_numParams_4249_);
lean_dec_ref(v_indVal_4240_);
v_levelParams_4250_ = lean_ctor_get(v_toConstantVal_4248_, 1);
lean_inc(v_levelParams_4250_);
v_type_4251_ = lean_ctor_get(v_toConstantVal_4248_, 2);
lean_inc_ref(v_type_4251_);
lean_dec_ref(v_toConstantVal_4248_);
v___f_4252_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4253_ = lean_box(1);
v___x_4254_ = lean_box(0);
v_us_4255_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4250_, v___x_4254_);
v___x_4256_ = lean_box(v_addHypotheses_4239_);
v___f_4257_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4257_, 0, v_numParams_4249_);
lean_closure_set(v___f_4257_, 1, v_inductiveTypeName_4237_);
lean_closure_set(v___f_4257_, 2, v_us_4255_);
lean_closure_set(v___f_4257_, 3, v___x_4253_);
lean_closure_set(v___f_4257_, 4, v_ctorName_4238_);
lean_closure_set(v___f_4257_, 5, v___f_4252_);
lean_closure_set(v___f_4257_, 6, v___x_4256_);
v___x_4258_ = 0;
v___x_4259_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4251_, v___f_4257_, v___x_4258_, v___x_4258_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4260_, lean_object* v_ctorName_4261_, lean_object* v_addHypotheses_4262_, lean_object* v_indVal_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
uint8_t v_addHypotheses_boxed_4271_; lean_object* v_res_4272_; 
v_addHypotheses_boxed_4271_ = lean_unbox(v_addHypotheses_4262_);
v_res_4272_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4260_, v_ctorName_4261_, v_addHypotheses_boxed_4271_, v_indVal_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
lean_dec(v_a_4269_);
lean_dec_ref(v_a_4268_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4273_, lean_object* v_bs_4274_, lean_object* v_k_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4274_, v_k_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4284_, lean_object* v_bs_4285_, lean_object* v_k_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4284_, v_bs_4285_, v_k_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v_bs_4285_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4295_, lean_object* v_bs_4296_, lean_object* v_k_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4296_, v_k_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4306_, lean_object* v_bs_4307_, lean_object* v_k_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4306_, v_bs_4307_, v_k_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4317_, lean_object* v_levelParams_4318_, lean_object* v_type_4319_, lean_object* v_value_4320_, lean_object* v_hints_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v___x_4324_; uint8_t v___y_4326_; uint8_t v___y_4333_; lean_object* v_env_4336_; uint8_t v___x_4337_; 
v___x_4324_ = lean_st_ref_get(v___y_4322_);
v_env_4336_ = lean_ctor_get(v___x_4324_, 0);
lean_inc_ref_n(v_env_4336_, 2);
lean_dec(v___x_4324_);
v___x_4337_ = l_Lean_Environment_hasUnsafe(v_env_4336_, v_type_4319_);
if (v___x_4337_ == 0)
{
uint8_t v___x_4338_; 
v___x_4338_ = l_Lean_Environment_hasUnsafe(v_env_4336_, v_value_4320_);
v___y_4333_ = v___x_4338_;
goto v___jp_4332_;
}
else
{
lean_dec_ref(v_env_4336_);
v___y_4333_ = v___x_4337_;
goto v___jp_4332_;
}
v___jp_4325_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
lean_inc(v_name_4317_);
v___x_4327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4327_, 0, v_name_4317_);
lean_ctor_set(v___x_4327_, 1, v_levelParams_4318_);
lean_ctor_set(v___x_4327_, 2, v_type_4319_);
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4329_, 0, v_name_4317_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4330_, 0, v___x_4327_);
lean_ctor_set(v___x_4330_, 1, v_value_4320_);
lean_ctor_set(v___x_4330_, 2, v_hints_4321_);
lean_ctor_set(v___x_4330_, 3, v___x_4329_);
lean_ctor_set_uint8(v___x_4330_, sizeof(void*)*4, v___y_4326_);
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
return v___x_4331_;
}
v___jp_4332_:
{
if (v___y_4333_ == 0)
{
uint8_t v___x_4334_; 
v___x_4334_ = 1;
v___y_4326_ = v___x_4334_;
goto v___jp_4325_;
}
else
{
uint8_t v___x_4335_; 
v___x_4335_ = 0;
v___y_4326_ = v___x_4335_;
goto v___jp_4325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4339_, lean_object* v_levelParams_4340_, lean_object* v_type_4341_, lean_object* v_value_4342_, lean_object* v_hints_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4339_, v_levelParams_4340_, v_type_4341_, v_value_4342_, v_hints_4343_, v___y_4344_);
lean_dec(v___y_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4347_, lean_object* v_levelParams_4348_, lean_object* v_type_4349_, lean_object* v_value_4350_, lean_object* v_hints_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4347_, v_levelParams_4348_, v_type_4349_, v_value_4350_, v_hints_4351_, v___y_4357_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4360_, lean_object* v_levelParams_4361_, lean_object* v_type_4362_, lean_object* v_value_4363_, lean_object* v_hints_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4360_, v_levelParams_4361_, v_type_4362_, v_value_4363_, v_hints_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4373_, uint8_t v_isExporting_4374_, lean_object* v___x_4375_, lean_object* v___y_4376_, lean_object* v___x_4377_, lean_object* v_a_x3f_4378_){
_start:
{
lean_object* v___x_4380_; lean_object* v_env_4381_; lean_object* v_nextMacroScope_4382_; lean_object* v_ngen_4383_; lean_object* v_auxDeclNGen_4384_; lean_object* v_traceState_4385_; lean_object* v_messages_4386_; lean_object* v_infoState_4387_; lean_object* v_snapshotTasks_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4413_; 
v___x_4380_ = lean_st_ref_take(v___y_4373_);
v_env_4381_ = lean_ctor_get(v___x_4380_, 0);
v_nextMacroScope_4382_ = lean_ctor_get(v___x_4380_, 1);
v_ngen_4383_ = lean_ctor_get(v___x_4380_, 2);
v_auxDeclNGen_4384_ = lean_ctor_get(v___x_4380_, 3);
v_traceState_4385_ = lean_ctor_get(v___x_4380_, 4);
v_messages_4386_ = lean_ctor_get(v___x_4380_, 6);
v_infoState_4387_ = lean_ctor_get(v___x_4380_, 7);
v_snapshotTasks_4388_ = lean_ctor_get(v___x_4380_, 8);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; 
v_unused_4414_ = lean_ctor_get(v___x_4380_, 5);
lean_dec(v_unused_4414_);
v___x_4390_ = v___x_4380_;
v_isShared_4391_ = v_isSharedCheck_4413_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_snapshotTasks_4388_);
lean_inc(v_infoState_4387_);
lean_inc(v_messages_4386_);
lean_inc(v_traceState_4385_);
lean_inc(v_auxDeclNGen_4384_);
lean_inc(v_ngen_4383_);
lean_inc(v_nextMacroScope_4382_);
lean_inc(v_env_4381_);
lean_dec(v___x_4380_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4413_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4392_ = l_Lean_Environment_setExporting(v_env_4381_, v_isExporting_4374_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 5, v___x_4375_);
lean_ctor_set(v___x_4390_, 0, v___x_4392_);
v___x_4394_ = v___x_4390_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_nextMacroScope_4382_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_ngen_4383_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v_auxDeclNGen_4384_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_traceState_4385_);
lean_ctor_set(v_reuseFailAlloc_4412_, 5, v___x_4375_);
lean_ctor_set(v_reuseFailAlloc_4412_, 6, v_messages_4386_);
lean_ctor_set(v_reuseFailAlloc_4412_, 7, v_infoState_4387_);
lean_ctor_set(v_reuseFailAlloc_4412_, 8, v_snapshotTasks_4388_);
v___x_4394_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v_mctx_4397_; lean_object* v_zetaDeltaFVarIds_4398_; lean_object* v_postponed_4399_; lean_object* v_diag_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4410_; 
v___x_4395_ = lean_st_ref_put(v___y_4373_, v___x_4394_);
v___x_4396_ = lean_st_ref_take(v___y_4376_);
v_mctx_4397_ = lean_ctor_get(v___x_4396_, 0);
v_zetaDeltaFVarIds_4398_ = lean_ctor_get(v___x_4396_, 2);
v_postponed_4399_ = lean_ctor_get(v___x_4396_, 3);
v_diag_4400_ = lean_ctor_get(v___x_4396_, 4);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; 
v_unused_4411_ = lean_ctor_get(v___x_4396_, 1);
lean_dec(v_unused_4411_);
v___x_4402_ = v___x_4396_;
v_isShared_4403_ = v_isSharedCheck_4410_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_diag_4400_);
lean_inc(v_postponed_4399_);
lean_inc(v_zetaDeltaFVarIds_4398_);
lean_inc(v_mctx_4397_);
lean_dec(v___x_4396_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4410_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 1, v___x_4377_);
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_mctx_4397_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v___x_4377_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v_zetaDeltaFVarIds_4398_);
lean_ctor_set(v_reuseFailAlloc_4409_, 3, v_postponed_4399_);
lean_ctor_set(v_reuseFailAlloc_4409_, 4, v_diag_4400_);
v___x_4405_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4406_ = lean_st_ref_put(v___y_4376_, v___x_4405_);
v___x_4407_ = lean_box(0);
v___x_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
return v___x_4408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4415_, lean_object* v_isExporting_4416_, lean_object* v___x_4417_, lean_object* v___y_4418_, lean_object* v___x_4419_, lean_object* v_a_x3f_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v_isExporting_boxed_4422_; lean_object* v_res_4423_; 
v_isExporting_boxed_4422_ = lean_unbox(v_isExporting_4416_);
v_res_4423_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4415_, v_isExporting_boxed_4422_, v___x_4417_, v___y_4418_, v___x_4419_, v_a_x3f_4420_);
lean_dec(v_a_x3f_4420_);
lean_dec(v___y_4418_);
lean_dec(v___y_4415_);
return v_res_4423_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4424_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
return v___x_4426_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
lean_ctor_set(v___x_4428_, 1, v___x_4427_);
return v___x_4428_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4430_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
lean_ctor_set(v___x_4430_, 2, v___x_4429_);
lean_ctor_set(v___x_4430_, 3, v___x_4429_);
lean_ctor_set(v___x_4430_, 4, v___x_4429_);
lean_ctor_set(v___x_4430_, 5, v___x_4429_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4431_, uint8_t v_isExporting_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v___x_4440_; lean_object* v_env_4441_; uint8_t v_isExporting_4442_; lean_object* v___x_4508_; uint8_t v_isModule_4509_; 
v___x_4440_ = lean_st_ref_get(v___y_4438_);
v_env_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc_ref(v_env_4441_);
lean_dec(v___x_4440_);
v_isExporting_4442_ = lean_ctor_get_uint8(v_env_4441_, sizeof(void*)*8);
v___x_4508_ = l_Lean_Environment_header(v_env_4441_);
lean_dec_ref(v_env_4441_);
v_isModule_4509_ = lean_ctor_get_uint8(v___x_4508_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4508_);
if (v_isModule_4509_ == 0)
{
lean_object* v___x_4510_; 
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
lean_inc(v___y_4436_);
lean_inc_ref(v___y_4435_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
v___x_4510_ = lean_apply_7(v_x_4431_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, lean_box(0));
return v___x_4510_;
}
else
{
if (v_isExporting_4442_ == 0)
{
if (v_isExporting_4432_ == 0)
{
lean_object* v___x_4511_; 
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
lean_inc(v___y_4436_);
lean_inc_ref(v___y_4435_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
v___x_4511_ = lean_apply_7(v_x_4431_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, lean_box(0));
return v___x_4511_;
}
else
{
goto v___jp_4443_;
}
}
else
{
if (v_isExporting_4432_ == 0)
{
goto v___jp_4443_;
}
else
{
lean_object* v___x_4512_; 
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
lean_inc(v___y_4436_);
lean_inc_ref(v___y_4435_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
v___x_4512_ = lean_apply_7(v_x_4431_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, lean_box(0));
return v___x_4512_;
}
}
}
v___jp_4443_:
{
lean_object* v___x_4444_; lean_object* v_env_4445_; lean_object* v_nextMacroScope_4446_; lean_object* v_ngen_4447_; lean_object* v_auxDeclNGen_4448_; lean_object* v_traceState_4449_; lean_object* v_messages_4450_; lean_object* v_infoState_4451_; lean_object* v_snapshotTasks_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4506_; 
v___x_4444_ = lean_st_ref_take(v___y_4438_);
v_env_4445_ = lean_ctor_get(v___x_4444_, 0);
v_nextMacroScope_4446_ = lean_ctor_get(v___x_4444_, 1);
v_ngen_4447_ = lean_ctor_get(v___x_4444_, 2);
v_auxDeclNGen_4448_ = lean_ctor_get(v___x_4444_, 3);
v_traceState_4449_ = lean_ctor_get(v___x_4444_, 4);
v_messages_4450_ = lean_ctor_get(v___x_4444_, 6);
v_infoState_4451_ = lean_ctor_get(v___x_4444_, 7);
v_snapshotTasks_4452_ = lean_ctor_get(v___x_4444_, 8);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4506_ == 0)
{
lean_object* v_unused_4507_; 
v_unused_4507_ = lean_ctor_get(v___x_4444_, 5);
lean_dec(v_unused_4507_);
v___x_4454_ = v___x_4444_;
v_isShared_4455_ = v_isSharedCheck_4506_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_snapshotTasks_4452_);
lean_inc(v_infoState_4451_);
lean_inc(v_messages_4450_);
lean_inc(v_traceState_4449_);
lean_inc(v_auxDeclNGen_4448_);
lean_inc(v_ngen_4447_);
lean_inc(v_nextMacroScope_4446_);
lean_inc(v_env_4445_);
lean_dec(v___x_4444_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4506_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4456_ = l_Lean_Environment_setExporting(v_env_4445_, v_isExporting_4432_);
v___x_4457_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 5, v___x_4457_);
lean_ctor_set(v___x_4454_, 0, v___x_4456_);
v___x_4459_ = v___x_4454_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4456_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_nextMacroScope_4446_);
lean_ctor_set(v_reuseFailAlloc_4505_, 2, v_ngen_4447_);
lean_ctor_set(v_reuseFailAlloc_4505_, 3, v_auxDeclNGen_4448_);
lean_ctor_set(v_reuseFailAlloc_4505_, 4, v_traceState_4449_);
lean_ctor_set(v_reuseFailAlloc_4505_, 5, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4505_, 6, v_messages_4450_);
lean_ctor_set(v_reuseFailAlloc_4505_, 7, v_infoState_4451_);
lean_ctor_set(v_reuseFailAlloc_4505_, 8, v_snapshotTasks_4452_);
v___x_4459_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v_mctx_4462_; lean_object* v_zetaDeltaFVarIds_4463_; lean_object* v_postponed_4464_; lean_object* v_diag_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4503_; 
v___x_4460_ = lean_st_ref_put(v___y_4438_, v___x_4459_);
v___x_4461_ = lean_st_ref_take(v___y_4436_);
v_mctx_4462_ = lean_ctor_get(v___x_4461_, 0);
v_zetaDeltaFVarIds_4463_ = lean_ctor_get(v___x_4461_, 2);
v_postponed_4464_ = lean_ctor_get(v___x_4461_, 3);
v_diag_4465_ = lean_ctor_get(v___x_4461_, 4);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v___x_4461_, 1);
lean_dec(v_unused_4504_);
v___x_4467_ = v___x_4461_;
v_isShared_4468_ = v_isSharedCheck_4503_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_diag_4465_);
lean_inc(v_postponed_4464_);
lean_inc(v_zetaDeltaFVarIds_4463_);
lean_inc(v_mctx_4462_);
lean_dec(v___x_4461_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4503_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4469_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 1, v___x_4469_);
v___x_4471_ = v___x_4467_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_mctx_4462_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_zetaDeltaFVarIds_4463_);
lean_ctor_set(v_reuseFailAlloc_4502_, 3, v_postponed_4464_);
lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_diag_4465_);
v___x_4471_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; lean_object* v_r_4473_; 
v___x_4472_ = lean_st_ref_put(v___y_4436_, v___x_4471_);
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
lean_inc(v___y_4436_);
lean_inc_ref(v___y_4435_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
v_r_4473_ = lean_apply_7(v_x_4431_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, lean_box(0));
if (lean_obj_tag(v_r_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4490_; 
v_a_4474_ = lean_ctor_get(v_r_4473_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_r_4473_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4476_ = v_r_4473_;
v_isShared_4477_ = v_isSharedCheck_4490_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v_r_4473_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4490_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
lean_inc(v_a_4474_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set_tag(v___x_4476_, 1);
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
lean_object* v___x_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
v___x_4480_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4438_, v_isExporting_4442_, v___x_4457_, v___y_4436_, v___x_4469_, v___x_4479_);
lean_dec_ref(v___x_4479_);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; 
v_unused_4488_ = lean_ctor_get(v___x_4480_, 0);
lean_dec(v_unused_4488_);
v___x_4482_ = v___x_4480_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_dec(v___x_4480_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v_a_4474_);
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4474_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
v_a_4491_ = lean_ctor_get(v_r_4473_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v_r_4473_, 1);
v___x_4492_ = lean_box(0);
v___x_4493_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4438_, v_isExporting_4442_, v___x_4457_, v___y_4436_, v___x_4469_, v___x_4492_);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v___x_4493_, 0);
lean_dec(v_unused_4501_);
v___x_4495_ = v___x_4493_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_dec(v___x_4493_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
lean_ctor_set_tag(v___x_4495_, 1);
lean_ctor_set(v___x_4495_, 0, v_a_4491_);
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4491_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4513_, lean_object* v_isExporting_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
uint8_t v_isExporting_boxed_4522_; lean_object* v_res_4523_; 
v_isExporting_boxed_4522_ = lean_unbox(v_isExporting_4514_);
v_res_4523_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4513_, v_isExporting_boxed_4522_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4524_, lean_object* v_x_4525_, uint8_t v_isExporting_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4525_, v_isExporting_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4535_, lean_object* v_x_4536_, lean_object* v_isExporting_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
uint8_t v_isExporting_boxed_4545_; lean_object* v_res_4546_; 
v_isExporting_boxed_4545_ = lean_unbox(v_isExporting_4537_);
v_res_4546_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4535_, v_x_4536_, v_isExporting_boxed_4545_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4557_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
return v_res_4567_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4570_ = l_Lean_stringToMessageData(v___x_4569_);
return v___x_4570_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4573_ = l_Lean_stringToMessageData(v___x_4572_);
return v___x_4573_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4575_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4576_ = l_Lean_stringToMessageData(v___x_4575_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4577_, lean_object* v___x_4578_, lean_object* v_inductiveTypeName_4579_, uint8_t v___x_4580_, lean_object* v___x_4581_, lean_object* v_ctorName_4582_, uint8_t v_addHypotheses_4583_, lean_object* v___f_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___y_4593_; lean_object* v___x_4596_; 
lean_inc(v_inductiveTypeName_4579_);
v___x_4596_ = l_Lean_Elab_Deriving_mkContext(v___x_4577_, v___x_4578_, v_inductiveTypeName_4579_, v___x_4580_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v_options_4598_; lean_object* v_currNamespace_4599_; lean_object* v_inheritedTraceOptions_4600_; lean_object* v___x_4601_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4596_, 1);
v_options_4598_ = lean_ctor_get(v___y_4589_, 2);
v_currNamespace_4599_ = lean_ctor_get(v___y_4589_, 6);
v_inheritedTraceOptions_4600_ = lean_ctor_get(v___y_4589_, 13);
lean_inc(v_inductiveTypeName_4579_);
v___x_4601_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4579_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v_instName_4603_; lean_object* v_auxFunNames_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; uint8_t v___y_4656_; lean_object* v___y_4657_; uint8_t v___y_4658_; lean_object* v___y_4696_; uint8_t v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v_a_4712_; lean_object* v___y_4783_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc_n(v_a_4602_, 2);
lean_dec_ref_known(v___x_4601_, 1);
v_instName_4603_ = lean_ctor_get(v_a_4597_, 0);
lean_inc(v_instName_4603_);
v_auxFunNames_4604_ = lean_ctor_get(v_a_4597_, 2);
lean_inc_ref(v_auxFunNames_4604_);
lean_dec(v_a_4597_);
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = lean_array_get(v___x_4581_, v_auxFunNames_4604_, v___x_4605_);
lean_dec_ref(v_auxFunNames_4604_);
lean_inc(v_currNamespace_4599_);
v___x_4607_ = l_Lean_Name_append(v_currNamespace_4599_, v___x_4606_);
v___x_4802_ = lean_box(v_addHypotheses_4583_);
lean_inc(v_inductiveTypeName_4579_);
v___x_4803_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4803_, 0, v_inductiveTypeName_4579_);
lean_closure_set(v___x_4803_, 1, v_ctorName_4582_);
lean_closure_set(v___x_4803_, 2, v___x_4802_);
lean_closure_set(v___x_4803_, 3, v_a_4602_);
lean_inc(v___x_4607_);
v___x_4804_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4607_, v___x_4803_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; 
lean_dec_ref(v___f_4584_);
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4804_, 1);
v_a_4712_ = v_a_4805_;
goto v___jp_4711_;
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4838_; 
v_a_4806_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4808_ = v___x_4804_;
v_isShared_4809_ = v_isSharedCheck_4838_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4804_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4838_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
uint8_t v___y_4814_; uint8_t v___x_4836_; 
v___x_4836_ = l_Lean_Exception_isInterrupt(v_a_4806_);
if (v___x_4836_ == 0)
{
uint8_t v___x_4837_; 
lean_inc(v_a_4806_);
v___x_4837_ = l_Lean_Exception_isRuntime(v_a_4806_);
v___y_4814_ = v___x_4837_;
goto v___jp_4813_;
}
else
{
v___y_4814_ = v___x_4836_;
goto v___jp_4813_;
}
v___jp_4810_:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4811_ = lean_box(0);
lean_inc(v___y_4590_);
lean_inc_ref(v___y_4589_);
lean_inc(v___y_4588_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4586_);
lean_inc_ref(v___y_4585_);
v___x_4812_ = lean_apply_8(v___f_4584_, v___x_4811_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, lean_box(0));
v___y_4783_ = v___x_4812_;
goto v___jp_4782_;
}
v___jp_4813_:
{
if (v___y_4814_ == 0)
{
uint8_t v_hasTrace_4815_; 
lean_del_object(v___x_4808_);
v_hasTrace_4815_ = lean_ctor_get_uint8(v_options_4598_, sizeof(void*)*1);
if (v_hasTrace_4815_ == 0)
{
lean_dec(v_a_4806_);
goto v___jp_4810_;
}
else
{
lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v___x_4816_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4817_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4818_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4600_, v_options_4598_, v___x_4817_);
if (v___x_4818_ == 0)
{
lean_dec(v_a_4806_);
goto v___jp_4810_;
}
else
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4819_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4820_ = l_Lean_Exception_toMessageData(v_a_4806_);
v___x_4821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4819_);
lean_ctor_set(v___x_4821_, 1, v___x_4820_);
v___x_4822_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4816_, v___x_4821_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
lean_inc(v___y_4590_);
lean_inc_ref(v___y_4589_);
lean_inc(v___y_4588_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4586_);
lean_inc_ref(v___y_4585_);
v___x_4824_ = lean_apply_8(v___f_4584_, v_a_4823_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, lean_box(0));
v___y_4783_ = v___x_4824_;
goto v___jp_4782_;
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v_a_4602_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec_ref(v___f_4584_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4825_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4822_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4822_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
}
}
else
{
lean_object* v___x_4834_; 
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v_a_4602_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec_ref(v___f_4584_);
lean_dec(v_inductiveTypeName_4579_);
if (v_isShared_4809_ == 0)
{
v___x_4834_ = v___x_4808_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4806_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
}
v___jp_4608_:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4617_ = l_Lean_mkIdent(v_instName_4603_);
v___x_4618_ = l_Lean_mkCIdent(v___x_4607_);
v___x_4619_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4579_, v___x_4617_, v___y_4609_, v___x_4618_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4609_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_options_4620_; uint8_t v_hasTrace_4621_; 
v_options_4620_ = lean_ctor_get(v___y_4615_, 2);
v_hasTrace_4621_ = lean_ctor_get_uint8(v_options_4620_, sizeof(void*)*1);
if (v_hasTrace_4621_ == 0)
{
lean_object* v_a_4622_; 
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4610_);
v_a_4622_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4622_);
lean_dec_ref_known(v___x_4619_, 1);
v___y_4593_ = v_a_4622_;
goto v___jp_4592_;
}
else
{
lean_object* v_a_4623_; lean_object* v_inheritedTraceOptions_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; 
v_a_4623_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4623_);
lean_dec_ref_known(v___x_4619_, 1);
v_inheritedTraceOptions_4624_ = lean_ctor_get(v___y_4615_, 13);
v___x_4625_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4610_);
v___x_4626_ = l_Lean_Name_append(v___x_4625_, v___y_4610_);
v___x_4627_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4624_, v_options_4620_, v___x_4626_);
lean_dec(v___x_4626_);
if (v___x_4627_ == 0)
{
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4610_);
v___y_4593_ = v_a_4623_;
goto v___jp_4592_;
}
else
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4628_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4623_);
v___x_4629_ = l_Lean_MessageData_ofSyntax(v_a_4623_);
v___x_4630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4628_);
lean_ctor_set(v___x_4630_, 1, v___x_4629_);
v___x_4631_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4610_, v___x_4630_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_dec_ref_known(v___x_4631_, 1);
v___y_4593_ = v_a_4623_;
goto v___jp_4592_;
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_dec(v_a_4623_);
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4631_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4631_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4610_);
v_a_4640_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4619_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4619_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
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
v___jp_4648_:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Lean_compileDecls(v___y_4652_, v___y_4658_, v___y_4657_, v___y_4654_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v___x_4660_; 
lean_dec_ref_known(v___x_4659_, 1);
lean_inc(v___x_4607_);
v___x_4660_ = l_Lean_enableRealizationsForConst(v___x_4607_, v___y_4657_, v___y_4654_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_options_4661_; lean_object* v_inheritedTraceOptions_4662_; uint8_t v_hasTrace_4663_; lean_object* v___x_4664_; 
lean_dec_ref_known(v___x_4660_, 1);
v_options_4661_ = lean_ctor_get(v___y_4657_, 2);
v_inheritedTraceOptions_4662_ = lean_ctor_get(v___y_4657_, 13);
v_hasTrace_4663_ = lean_ctor_get_uint8(v_options_4661_, sizeof(void*)*1);
v___x_4664_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4663_ == 0)
{
v___y_4609_ = v___y_4650_;
v___y_4610_ = v___x_4664_;
v___y_4611_ = v___y_4649_;
v___y_4612_ = v___y_4653_;
v___y_4613_ = v___y_4655_;
v___y_4614_ = v___y_4651_;
v___y_4615_ = v___y_4657_;
v___y_4616_ = v___y_4654_;
goto v___jp_4608_;
}
else
{
lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4665_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4662_, v_options_4661_, v___x_4665_);
if (v___x_4666_ == 0)
{
v___y_4609_ = v___y_4650_;
v___y_4610_ = v___x_4664_;
v___y_4611_ = v___y_4649_;
v___y_4612_ = v___y_4653_;
v___y_4613_ = v___y_4655_;
v___y_4614_ = v___y_4651_;
v___y_4615_ = v___y_4657_;
v___y_4616_ = v___y_4654_;
goto v___jp_4608_;
}
else
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4667_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4607_);
v___x_4668_ = l_Lean_MessageData_ofConstName(v___x_4607_, v___y_4656_);
v___x_4669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4667_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
v___x_4670_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4664_, v___x_4669_, v___y_4655_, v___y_4651_, v___y_4657_, v___y_4654_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_dec_ref_known(v___x_4670_, 1);
v___y_4609_ = v___y_4650_;
v___y_4610_ = v___x_4664_;
v___y_4611_ = v___y_4649_;
v___y_4612_ = v___y_4653_;
v___y_4613_ = v___y_4655_;
v___y_4614_ = v___y_4651_;
v___y_4615_ = v___y_4657_;
v___y_4616_ = v___y_4654_;
goto v___jp_4608_;
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec_ref(v___y_4657_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_dec_ref(v___y_4657_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4679_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4660_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4660_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
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
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v___y_4657_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4687_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4659_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4659_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
v___jp_4695_:
{
lean_object* v___x_4704_; lean_object* v_env_4705_; uint8_t v_isNoncomputableSection_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4704_ = lean_st_ref_get(v___y_4703_);
v_env_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc_ref(v_env_4705_);
lean_dec(v___x_4704_);
v_isNoncomputableSection_4706_ = lean_ctor_get_uint8(v___y_4698_, sizeof(void*)*8 + 4);
v___x_4707_ = lean_unsigned_to_nat(1u);
v___x_4708_ = lean_mk_empty_array_with_capacity(v___x_4707_);
lean_inc(v___x_4607_);
v___x_4709_ = lean_array_push(v___x_4708_, v___x_4607_);
if (v_isNoncomputableSection_4706_ == 0)
{
lean_dec_ref(v_env_4705_);
v___y_4649_ = v___y_4698_;
v___y_4650_ = v___y_4696_;
v___y_4651_ = v___y_4701_;
v___y_4652_ = v___x_4709_;
v___y_4653_ = v___y_4699_;
v___y_4654_ = v___y_4703_;
v___y_4655_ = v___y_4700_;
v___y_4656_ = v___y_4697_;
v___y_4657_ = v___y_4702_;
v___y_4658_ = v___x_4580_;
goto v___jp_4648_;
}
else
{
uint8_t v___x_4710_; 
lean_inc(v___x_4607_);
v___x_4710_ = l_Lean_isMarkedMeta(v_env_4705_, v___x_4607_);
v___y_4649_ = v___y_4698_;
v___y_4650_ = v___y_4696_;
v___y_4651_ = v___y_4701_;
v___y_4652_ = v___x_4709_;
v___y_4653_ = v___y_4699_;
v___y_4654_ = v___y_4703_;
v___y_4655_ = v___y_4700_;
v___y_4656_ = v___y_4697_;
v___y_4657_ = v___y_4702_;
v___y_4658_ = v___x_4710_;
goto v___jp_4648_;
}
}
v___jp_4711_:
{
lean_object* v_snd_4713_; lean_object* v_fst_4714_; lean_object* v_fst_4715_; lean_object* v_snd_4716_; lean_object* v___x_4717_; lean_object* v_toConstantVal_4718_; lean_object* v_env_4719_; lean_object* v_levelParams_4720_; uint32_t v___x_4721_; uint32_t v___x_4722_; uint32_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4781_; 
v_snd_4713_ = lean_ctor_get(v_a_4712_, 1);
lean_inc(v_snd_4713_);
v_fst_4714_ = lean_ctor_get(v_a_4712_, 0);
lean_inc(v_fst_4714_);
lean_dec_ref(v_a_4712_);
v_fst_4715_ = lean_ctor_get(v_snd_4713_, 0);
lean_inc_n(v_fst_4715_, 2);
v_snd_4716_ = lean_ctor_get(v_snd_4713_, 1);
lean_inc(v_snd_4716_);
lean_dec(v_snd_4713_);
v___x_4717_ = lean_st_ref_get(v___y_4590_);
v_toConstantVal_4718_ = lean_ctor_get(v_a_4602_, 0);
lean_inc_ref(v_toConstantVal_4718_);
lean_dec(v_a_4602_);
v_env_4719_ = lean_ctor_get(v___x_4717_, 0);
lean_inc_ref(v_env_4719_);
lean_dec(v___x_4717_);
v_levelParams_4720_ = lean_ctor_get(v_toConstantVal_4718_, 1);
lean_inc(v_levelParams_4720_);
lean_dec_ref(v_toConstantVal_4718_);
v___x_4721_ = l_Lean_getMaxHeight(v_env_4719_, v_fst_4715_);
v___x_4722_ = 1;
v___x_4723_ = lean_uint32_add(v___x_4721_, v___x_4722_);
v___x_4724_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4724_, 0, v___x_4723_);
lean_inc(v___x_4607_);
v___x_4725_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4607_, v_levelParams_4720_, v_fst_4714_, v_fst_4715_, v___x_4724_, v___y_4590_);
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4728_ = v___x_4725_;
v_isShared_4729_ = v_isSharedCheck_4781_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4725_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4781_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
lean_ctor_set_tag(v___x_4728_, 1);
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
uint8_t v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = 0;
v___x_4733_ = l_Lean_addDecl(v___x_4731_, v___x_4732_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v___x_4734_; lean_object* v_env_4735_; uint8_t v___x_4736_; 
lean_dec_ref_known(v___x_4733_, 1);
v___x_4734_ = lean_st_ref_get(v___y_4590_);
v_env_4735_ = lean_ctor_get(v___x_4734_, 0);
lean_inc_ref(v_env_4735_);
lean_dec(v___x_4734_);
lean_inc(v_inductiveTypeName_4579_);
v___x_4736_ = l_Lean_isMarkedMeta(v_env_4735_, v_inductiveTypeName_4579_);
if (v___x_4736_ == 0)
{
v___y_4696_ = v_snd_4716_;
v___y_4697_ = v___x_4732_;
v___y_4698_ = v___y_4585_;
v___y_4699_ = v___y_4586_;
v___y_4700_ = v___y_4587_;
v___y_4701_ = v___y_4588_;
v___y_4702_ = v___y_4589_;
v___y_4703_ = v___y_4590_;
goto v___jp_4695_;
}
else
{
lean_object* v___x_4737_; lean_object* v_env_4738_; lean_object* v_nextMacroScope_4739_; lean_object* v_ngen_4740_; lean_object* v_auxDeclNGen_4741_; lean_object* v_traceState_4742_; lean_object* v_messages_4743_; lean_object* v_infoState_4744_; lean_object* v_snapshotTasks_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4770_; 
v___x_4737_ = lean_st_ref_take(v___y_4590_);
v_env_4738_ = lean_ctor_get(v___x_4737_, 0);
v_nextMacroScope_4739_ = lean_ctor_get(v___x_4737_, 1);
v_ngen_4740_ = lean_ctor_get(v___x_4737_, 2);
v_auxDeclNGen_4741_ = lean_ctor_get(v___x_4737_, 3);
v_traceState_4742_ = lean_ctor_get(v___x_4737_, 4);
v_messages_4743_ = lean_ctor_get(v___x_4737_, 6);
v_infoState_4744_ = lean_ctor_get(v___x_4737_, 7);
v_snapshotTasks_4745_ = lean_ctor_get(v___x_4737_, 8);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4770_ == 0)
{
lean_object* v_unused_4771_; 
v_unused_4771_ = lean_ctor_get(v___x_4737_, 5);
lean_dec(v_unused_4771_);
v___x_4747_ = v___x_4737_;
v_isShared_4748_ = v_isSharedCheck_4770_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_snapshotTasks_4745_);
lean_inc(v_infoState_4744_);
lean_inc(v_messages_4743_);
lean_inc(v_traceState_4742_);
lean_inc(v_auxDeclNGen_4741_);
lean_inc(v_ngen_4740_);
lean_inc(v_nextMacroScope_4739_);
lean_inc(v_env_4738_);
lean_dec(v___x_4737_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4770_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4752_; 
lean_inc(v___x_4607_);
v___x_4749_ = l_Lean_markMeta(v_env_4738_, v___x_4607_);
v___x_4750_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 5, v___x_4750_);
lean_ctor_set(v___x_4747_, 0, v___x_4749_);
v___x_4752_ = v___x_4747_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4749_);
lean_ctor_set(v_reuseFailAlloc_4769_, 1, v_nextMacroScope_4739_);
lean_ctor_set(v_reuseFailAlloc_4769_, 2, v_ngen_4740_);
lean_ctor_set(v_reuseFailAlloc_4769_, 3, v_auxDeclNGen_4741_);
lean_ctor_set(v_reuseFailAlloc_4769_, 4, v_traceState_4742_);
lean_ctor_set(v_reuseFailAlloc_4769_, 5, v___x_4750_);
lean_ctor_set(v_reuseFailAlloc_4769_, 6, v_messages_4743_);
lean_ctor_set(v_reuseFailAlloc_4769_, 7, v_infoState_4744_);
lean_ctor_set(v_reuseFailAlloc_4769_, 8, v_snapshotTasks_4745_);
v___x_4752_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v_mctx_4755_; lean_object* v_zetaDeltaFVarIds_4756_; lean_object* v_postponed_4757_; lean_object* v_diag_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4767_; 
v___x_4753_ = lean_st_ref_put(v___y_4590_, v___x_4752_);
v___x_4754_ = lean_st_ref_take(v___y_4588_);
v_mctx_4755_ = lean_ctor_get(v___x_4754_, 0);
v_zetaDeltaFVarIds_4756_ = lean_ctor_get(v___x_4754_, 2);
v_postponed_4757_ = lean_ctor_get(v___x_4754_, 3);
v_diag_4758_ = lean_ctor_get(v___x_4754_, 4);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4767_ == 0)
{
lean_object* v_unused_4768_; 
v_unused_4768_ = lean_ctor_get(v___x_4754_, 1);
lean_dec(v_unused_4768_);
v___x_4760_ = v___x_4754_;
v_isShared_4761_ = v_isSharedCheck_4767_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_diag_4758_);
lean_inc(v_postponed_4757_);
lean_inc(v_zetaDeltaFVarIds_4756_);
lean_inc(v_mctx_4755_);
lean_dec(v___x_4754_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4767_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4762_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 1, v___x_4762_);
v___x_4764_ = v___x_4760_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_mctx_4755_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v___x_4762_);
lean_ctor_set(v_reuseFailAlloc_4766_, 2, v_zetaDeltaFVarIds_4756_);
lean_ctor_set(v_reuseFailAlloc_4766_, 3, v_postponed_4757_);
lean_ctor_set(v_reuseFailAlloc_4766_, 4, v_diag_4758_);
v___x_4764_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4765_; 
v___x_4765_ = lean_st_ref_put(v___y_4588_, v___x_4764_);
v___y_4696_ = v_snd_4716_;
v___y_4697_ = v___x_4732_;
v___y_4698_ = v___y_4585_;
v___y_4699_ = v___y_4586_;
v___y_4700_ = v___y_4587_;
v___y_4701_ = v___y_4588_;
v___y_4702_ = v___y_4589_;
v___y_4703_ = v___y_4590_;
goto v___jp_4695_;
}
}
}
}
}
}
else
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4779_; 
lean_dec(v_snd_4716_);
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4772_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4774_ = v___x_4733_;
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4733_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4777_; 
if (v_isShared_4775_ == 0)
{
v___x_4777_ = v___x_4774_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4772_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
}
}
}
v___jp_4782_:
{
if (lean_obj_tag(v___y_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4793_; 
v_a_4784_ = lean_ctor_get(v___y_4783_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___y_4783_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4786_ = v___y_4783_;
v_isShared_4787_ = v_isSharedCheck_4793_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___y_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4793_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
if (lean_obj_tag(v_a_4784_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4790_; 
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v_a_4602_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4788_ = lean_ctor_get(v_a_4784_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v_a_4784_, 1);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v_a_4788_);
v___x_4790_ = v___x_4786_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4788_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
else
{
lean_object* v_a_4792_; 
lean_del_object(v___x_4786_);
v_a_4792_ = lean_ctor_get(v_a_4784_, 0);
lean_inc(v_a_4792_);
lean_dec_ref_known(v_a_4784_, 1);
v_a_4712_ = v_a_4792_;
goto v___jp_4711_;
}
}
}
else
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
lean_dec(v___x_4607_);
lean_dec(v_instName_4603_);
lean_dec(v_a_4602_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4794_ = lean_ctor_get(v___y_4783_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___y_4783_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___y_4783_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___y_4783_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec(v_a_4597_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec_ref(v___f_4584_);
lean_dec(v_ctorName_4582_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4839_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4601_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4601_);
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
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec_ref(v___f_4584_);
lean_dec(v_ctorName_4582_);
lean_dec(v_inductiveTypeName_4579_);
v_a_4847_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4596_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4596_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
v___jp_4592_:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4594_, 0, v___y_4593_);
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4855_, lean_object* v___x_4856_, lean_object* v_inductiveTypeName_4857_, lean_object* v___x_4858_, lean_object* v___x_4859_, lean_object* v_ctorName_4860_, lean_object* v_addHypotheses_4861_, lean_object* v___f_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
uint8_t v___x_17618__boxed_4870_; uint8_t v_addHypotheses_boxed_4871_; lean_object* v_res_4872_; 
v___x_17618__boxed_4870_ = lean_unbox(v___x_4858_);
v_addHypotheses_boxed_4871_ = lean_unbox(v_addHypotheses_4861_);
v_res_4872_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4855_, v___x_4856_, v_inductiveTypeName_4857_, v___x_17618__boxed_4870_, v___x_4859_, v_ctorName_4860_, v_addHypotheses_boxed_4871_, v___f_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
lean_dec(v___x_4859_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4875_, lean_object* v_ctorName_4876_, uint8_t v_addHypotheses_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___f_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; uint8_t v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___f_4892_; uint8_t v___x_4893_; 
v___f_4885_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4886_ = lean_box(0);
v___x_4887_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4888_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4889_ = 1;
v___x_4890_ = lean_box(v___x_4889_);
v___x_4891_ = lean_box(v_addHypotheses_4877_);
lean_inc(v_ctorName_4876_);
v___f_4892_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4892_, 0, v___x_4887_);
lean_closure_set(v___f_4892_, 1, v___x_4888_);
lean_closure_set(v___f_4892_, 2, v_inductiveTypeName_4875_);
lean_closure_set(v___f_4892_, 3, v___x_4890_);
lean_closure_set(v___f_4892_, 4, v___x_4886_);
lean_closure_set(v___f_4892_, 5, v_ctorName_4876_);
lean_closure_set(v___f_4892_, 6, v___x_4891_);
lean_closure_set(v___f_4892_, 7, v___f_4885_);
v___x_4893_ = l_Lean_isPrivateName(v_ctorName_4876_);
lean_dec(v_ctorName_4876_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; 
v___x_4894_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4892_, v___x_4889_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
return v___x_4894_;
}
else
{
uint8_t v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = 0;
v___x_4896_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4892_, v___x_4895_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
return v___x_4896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4897_, lean_object* v_ctorName_4898_, lean_object* v_addHypotheses_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_){
_start:
{
uint8_t v_addHypotheses_boxed_4907_; lean_object* v_res_4908_; 
v_addHypotheses_boxed_4907_ = lean_unbox(v_addHypotheses_4899_);
v_res_4908_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4897_, v_ctorName_4898_, v_addHypotheses_boxed_4907_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
lean_dec_ref(v_a_4900_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4909_, lean_object* v_ctorName_4910_, uint8_t v_addHypotheses_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4915_ = lean_box(v_addHypotheses_4911_);
v___x_4916_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4916_, 0, v_inductiveTypeName_4909_);
lean_closure_set(v___x_4916_, 1, v_ctorName_4910_);
lean_closure_set(v___x_4916_, 2, v___x_4915_);
v___x_4917_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4916_, v_a_4912_, v_a_4913_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4947_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4947_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4947_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
if (lean_obj_tag(v_a_4918_) == 0)
{
uint8_t v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4925_; 
v___x_4922_ = 0;
v___x_4923_ = lean_box(v___x_4922_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4923_);
v___x_4925_ = v___x_4920_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
else
{
lean_object* v_val_4927_; lean_object* v___x_4928_; 
lean_del_object(v___x_4920_);
v_val_4927_ = lean_ctor_get(v_a_4918_, 0);
lean_inc(v_val_4927_);
lean_dec_ref_known(v_a_4918_, 1);
v___x_4928_ = l_Lean_Elab_Command_elabCommand(v_val_4927_, v_a_4912_, v_a_4913_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4937_; 
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4937_ == 0)
{
lean_object* v_unused_4938_; 
v_unused_4938_ = lean_ctor_get(v___x_4928_, 0);
lean_dec(v_unused_4938_);
v___x_4930_ = v___x_4928_;
v_isShared_4931_ = v_isSharedCheck_4937_;
goto v_resetjp_4929_;
}
else
{
lean_dec(v___x_4928_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4937_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
uint8_t v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v___x_4932_ = 1;
v___x_4933_ = lean_box(v___x_4932_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v___x_4933_);
v___x_4935_ = v___x_4930_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
else
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4946_; 
v_a_4939_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4941_ = v___x_4928_;
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4928_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4942_ == 0)
{
v___x_4944_ = v___x_4941_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4939_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
v_a_4948_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4917_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4917_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4956_, lean_object* v_ctorName_4957_, lean_object* v_addHypotheses_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
uint8_t v_addHypotheses_boxed_4962_; lean_object* v_res_4963_; 
v_addHypotheses_boxed_4962_ = lean_unbox(v_addHypotheses_4958_);
v_res_4963_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4956_, v_ctorName_4957_, v_addHypotheses_boxed_4962_, v_a_4959_, v_a_4960_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4967_, uint8_t v_addHypotheses_4968_, lean_object* v_as_x27_4969_, lean_object* v_b_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_){
_start:
{
if (lean_obj_tag(v_as_x27_4969_) == 0)
{
lean_object* v___x_4974_; 
lean_dec(v_declName_4967_);
v___x_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4974_, 0, v_b_4970_);
return v___x_4974_;
}
else
{
lean_object* v_head_4975_; lean_object* v_tail_4976_; lean_object* v___x_4977_; 
lean_dec_ref(v_b_4970_);
v_head_4975_ = lean_ctor_get(v_as_x27_4969_, 0);
v_tail_4976_ = lean_ctor_get(v_as_x27_4969_, 1);
lean_inc(v_head_4975_);
lean_inc(v_declName_4967_);
v___x_4977_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4967_, v_head_4975_, v_addHypotheses_4968_, v___y_4971_, v___y_4972_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4991_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4980_ = v___x_4977_;
v_isShared_4981_ = v_isSharedCheck_4991_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4977_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4991_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4982_; uint8_t v___x_4983_; 
v___x_4982_ = lean_box(0);
v___x_4983_ = lean_unbox(v_a_4978_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; 
lean_del_object(v___x_4980_);
lean_dec(v_a_4978_);
v___x_4984_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v_as_x27_4969_ = v_tail_4976_;
v_b_4970_ = v___x_4984_;
goto _start;
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4989_; 
lean_dec(v_declName_4967_);
v___x_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4986_, 0, v_a_4978_);
v___x_4987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
lean_ctor_set(v___x_4987_, 1, v___x_4982_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 0, v___x_4987_);
v___x_4989_ = v___x_4980_;
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
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec(v_declName_4967_);
v_a_4992_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4977_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4977_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_5000_, lean_object* v_addHypotheses_5001_, lean_object* v_as_x27_5002_, lean_object* v_b_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
uint8_t v_addHypotheses_boxed_5007_; lean_object* v_res_5008_; 
v_addHypotheses_boxed_5007_ = lean_unbox(v_addHypotheses_5001_);
v_res_5008_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5000_, v_addHypotheses_boxed_5007_, v_as_x27_5002_, v_b_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v_as_x27_5002_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_5009_, lean_object* v_declName_5010_, uint8_t v_addHypotheses_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_){
_start:
{
lean_object* v_ctors_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v_ctors_5015_ = lean_ctor_get(v_a_5009_, 4);
v___x_5016_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_5017_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5010_, v_addHypotheses_5011_, v_ctors_5015_, v___x_5016_, v___y_5012_, v___y_5013_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5032_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5032_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5032_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v_fst_5022_; 
v_fst_5022_ = lean_ctor_get(v_a_5018_, 0);
lean_inc(v_fst_5022_);
lean_dec(v_a_5018_);
if (lean_obj_tag(v_fst_5022_) == 0)
{
uint8_t v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5023_ = 0;
v___x_5024_ = lean_box(v___x_5023_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 0, v___x_5024_);
v___x_5026_ = v___x_5020_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
else
{
lean_object* v_val_5028_; lean_object* v___x_5030_; 
v_val_5028_ = lean_ctor_get(v_fst_5022_, 0);
lean_inc(v_val_5028_);
lean_dec_ref_known(v_fst_5022_, 1);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 0, v_val_5028_);
v___x_5030_ = v___x_5020_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_val_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
v_a_5033_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5017_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5017_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_5041_, lean_object* v_declName_5042_, lean_object* v_addHypotheses_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
uint8_t v_addHypotheses_boxed_5047_; lean_object* v_res_5048_; 
v_addHypotheses_boxed_5047_ = lean_unbox(v_addHypotheses_5043_);
v_res_5048_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5041_, v_declName_5042_, v_addHypotheses_boxed_5047_, v___y_5044_, v___y_5045_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
lean_dec_ref(v_a_5041_);
return v_res_5048_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_5049_; 
v___x_5049_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5049_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
return v___x_5051_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_5053_ = lean_unsigned_to_nat(0u);
v___x_5054_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5053_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
lean_ctor_set(v___x_5054_, 2, v___x_5053_);
lean_ctor_set(v___x_5054_, 3, v___x_5053_);
lean_ctor_set(v___x_5054_, 4, v___x_5052_);
lean_ctor_set(v___x_5054_, 5, v___x_5052_);
lean_ctor_set(v___x_5054_, 6, v___x_5052_);
lean_ctor_set(v___x_5054_, 7, v___x_5052_);
lean_ctor_set(v___x_5054_, 8, v___x_5052_);
lean_ctor_set(v___x_5054_, 9, v___x_5052_);
lean_ctor_set(v___x_5054_, 10, v___x_5052_);
return v___x_5054_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5055_ = lean_unsigned_to_nat(32u);
v___x_5056_ = lean_mk_empty_array_with_capacity(v___x_5055_);
v___x_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
return v___x_5057_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5058_ = ((size_t)5ULL);
v___x_5059_ = lean_unsigned_to_nat(0u);
v___x_5060_ = lean_unsigned_to_nat(32u);
v___x_5061_ = lean_mk_empty_array_with_capacity(v___x_5060_);
v___x_5062_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_5063_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
lean_ctor_set(v___x_5063_, 1, v___x_5061_);
lean_ctor_set(v___x_5063_, 2, v___x_5059_);
lean_ctor_set(v___x_5063_, 3, v___x_5059_);
lean_ctor_set_usize(v___x_5063_, 4, v___x_5058_);
return v___x_5063_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5064_ = lean_box(1);
v___x_5065_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_5066_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_5067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
lean_ctor_set(v___x_5067_, 1, v___x_5065_);
lean_ctor_set(v___x_5067_, 2, v___x_5064_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v___x_5071_; lean_object* v_env_5072_; lean_object* v___x_5073_; lean_object* v_scopes_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v_opts_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5071_ = lean_st_ref_get(v___y_5069_);
v_env_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc_ref(v_env_5072_);
lean_dec(v___x_5071_);
v___x_5073_ = lean_st_ref_get(v___y_5069_);
v_scopes_5074_ = lean_ctor_get(v___x_5073_, 2);
lean_inc(v_scopes_5074_);
lean_dec(v___x_5073_);
v___x_5075_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5076_ = l_List_head_x21___redArg(v___x_5075_, v_scopes_5074_);
lean_dec(v_scopes_5074_);
v_opts_5077_ = lean_ctor_get(v___x_5076_, 1);
lean_inc_ref(v_opts_5077_);
lean_dec(v___x_5076_);
v___x_5078_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_5079_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5);
v___x_5080_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5080_, 0, v_env_5072_);
lean_ctor_set(v___x_5080_, 1, v___x_5078_);
lean_ctor_set(v___x_5080_, 2, v___x_5079_);
lean_ctor_set(v___x_5080_, 3, v_opts_5077_);
v___x_5081_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5080_);
lean_ctor_set(v___x_5081_, 1, v_msgData_5068_);
v___x_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5081_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5083_, v___y_5084_);
lean_dec(v___y_5084_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_5087_, lean_object* v_macroStack_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v___x_5091_; lean_object* v_scopes_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v_opts_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v___x_5091_ = lean_st_ref_get(v___y_5089_);
v_scopes_5092_ = lean_ctor_get(v___x_5091_, 2);
lean_inc(v_scopes_5092_);
lean_dec(v___x_5091_);
v___x_5093_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5094_ = l_List_head_x21___redArg(v___x_5093_, v_scopes_5092_);
lean_dec(v_scopes_5092_);
v_opts_5095_ = lean_ctor_get(v___x_5094_, 1);
lean_inc_ref(v_opts_5095_);
lean_dec(v___x_5094_);
v___x_5096_ = l_Lean_Elab_pp_macroStack;
v___x_5097_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_5095_, v___x_5096_);
lean_dec_ref(v_opts_5095_);
if (v___x_5097_ == 0)
{
lean_object* v___x_5098_; 
lean_dec(v_macroStack_5088_);
v___x_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5098_, 0, v_msgData_5087_);
return v___x_5098_;
}
else
{
if (lean_obj_tag(v_macroStack_5088_) == 0)
{
lean_object* v___x_5099_; 
v___x_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5099_, 0, v_msgData_5087_);
return v___x_5099_;
}
else
{
lean_object* v_head_5100_; lean_object* v_after_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5116_; 
v_head_5100_ = lean_ctor_get(v_macroStack_5088_, 0);
lean_inc(v_head_5100_);
v_after_5101_ = lean_ctor_get(v_head_5100_, 1);
v_isSharedCheck_5116_ = !lean_is_exclusive(v_head_5100_);
if (v_isSharedCheck_5116_ == 0)
{
lean_object* v_unused_5117_; 
v_unused_5117_ = lean_ctor_get(v_head_5100_, 0);
lean_dec(v_unused_5117_);
v___x_5103_ = v_head_5100_;
v_isShared_5104_ = v_isSharedCheck_5116_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_after_5101_);
lean_dec(v_head_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5116_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5105_; lean_object* v___x_5107_; 
v___x_5105_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_5104_ == 0)
{
lean_ctor_set_tag(v___x_5103_, 7);
lean_ctor_set(v___x_5103_, 1, v___x_5105_);
lean_ctor_set(v___x_5103_, 0, v_msgData_5087_);
v___x_5107_ = v___x_5103_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_msgData_5087_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v___x_5105_);
v___x_5107_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v_msgData_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5108_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_5109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5107_);
lean_ctor_set(v___x_5109_, 1, v___x_5108_);
v___x_5110_ = l_Lean_MessageData_ofSyntax(v_after_5101_);
v___x_5111_ = l_Lean_indentD(v___x_5110_);
v_msgData_5112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5112_, 0, v___x_5109_);
lean_ctor_set(v_msgData_5112_, 1, v___x_5111_);
v___x_5113_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_5112_, v_macroStack_5088_);
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
return v___x_5114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_5118_, lean_object* v_macroStack_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5118_, v_macroStack_5119_, v___y_5120_);
lean_dec(v___y_5120_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Lean_Elab_Command_getRef___redArg(v___y_5124_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v_macroStack_5129_; lean_object* v___x_5130_; lean_object* v_a_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5142_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5127_, 1);
v_macroStack_5129_ = lean_ctor_get(v___y_5124_, 4);
v___x_5130_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_5123_, v___y_5125_);
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref(v___x_5130_);
v___x_5132_ = l_Lean_Elab_getBetterRef(v_a_5128_, v_macroStack_5129_);
lean_dec(v_a_5128_);
lean_inc(v_macroStack_5129_);
v___x_5133_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_5131_, v_macroStack_5129_, v___y_5125_);
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5136_ = v___x_5133_;
v_isShared_5137_ = v_isSharedCheck_5142_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5133_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5142_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5138_; lean_object* v___x_5140_; 
v___x_5138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5132_);
lean_ctor_set(v___x_5138_, 1, v_a_5134_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set_tag(v___x_5136_, 1);
lean_ctor_set(v___x_5136_, 0, v___x_5138_);
v___x_5140_ = v___x_5136_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5138_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec_ref(v_msg_5123_);
v_a_5143_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5127_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5127_);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5151_, v___y_5152_, v___y_5153_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_){
_start:
{
lean_object* v___x_5160_; lean_object* v_env_5161_; lean_object* v___x_5162_; 
v___x_5160_ = lean_st_ref_get(v___y_5158_);
v_env_5161_ = lean_ctor_get(v___x_5160_, 0);
lean_inc_ref(v_env_5161_);
lean_dec(v___x_5160_);
lean_inc(v_constName_5156_);
v___x_5162_ = l_Lean_isInductiveCore_x3f(v_env_5161_, v_constName_5156_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v___x_5163_; uint8_t v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5163_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5164_ = 0;
v___x_5165_ = l_Lean_MessageData_ofConstName(v_constName_5156_, v___x_5164_);
v___x_5166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5163_);
lean_ctor_set(v___x_5166_, 1, v___x_5165_);
v___x_5167_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5168_, v___y_5157_, v___y_5158_);
return v___x_5169_;
}
else
{
lean_object* v_val_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5177_; 
lean_dec(v_constName_5156_);
v_val_5170_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5172_ = v___x_5162_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_val_5170_);
lean_dec(v___x_5162_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5175_; 
if (v_isShared_5173_ == 0)
{
lean_ctor_set_tag(v___x_5172_, 0);
v___x_5175_ = v___x_5172_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_val_5170_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5178_, v___y_5179_, v___y_5180_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
return v_res_5182_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5184_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5185_ = l_Lean_stringToMessageData(v___x_5184_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v___x_5193_; 
lean_inc(v_declName_5186_);
v___x_5193_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5186_, v___y_5187_, v___y_5188_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v_a_5194_; uint8_t v___x_5195_; lean_object* v___x_5196_; 
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
lean_inc(v_a_5194_);
lean_dec_ref_known(v___x_5193_, 1);
v___x_5195_ = 0;
lean_inc(v_declName_5186_);
v___x_5196_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5194_, v_declName_5186_, v___x_5195_, v___y_5187_, v___y_5188_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_a_5197_; uint8_t v___x_5198_; 
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
lean_inc(v_a_5197_);
lean_dec_ref_known(v___x_5196_, 1);
v___x_5198_ = lean_unbox(v_a_5197_);
lean_dec(v_a_5197_);
if (v___x_5198_ == 0)
{
uint8_t v___x_5199_; lean_object* v___x_5200_; 
v___x_5199_ = 1;
lean_inc(v_declName_5186_);
v___x_5200_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5194_, v_declName_5186_, v___x_5199_, v___y_5187_, v___y_5188_);
lean_dec(v_a_5194_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; uint8_t v___x_5202_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5200_, 1);
v___x_5202_ = lean_unbox(v_a_5201_);
lean_dec(v_a_5201_);
if (v___x_5202_ == 0)
{
lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5203_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5204_ = l_Lean_MessageData_ofConstName(v_declName_5186_, v___x_5195_);
v___x_5205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5203_);
lean_ctor_set(v___x_5205_, 1, v___x_5204_);
v___x_5206_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5205_);
lean_ctor_set(v___x_5207_, 1, v___x_5206_);
v___x_5208_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5207_, v___y_5187_, v___y_5188_);
return v___x_5208_;
}
else
{
lean_dec(v_declName_5186_);
goto v___jp_5190_;
}
}
else
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5216_; 
lean_dec(v_declName_5186_);
v_a_5209_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5211_ = v___x_5200_;
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5200_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
else
{
lean_dec(v_a_5194_);
lean_dec(v_declName_5186_);
goto v___jp_5190_;
}
}
else
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5224_; 
lean_dec(v_a_5194_);
lean_dec(v_declName_5186_);
v_a_5217_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5219_ = v___x_5196_;
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5196_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5222_; 
if (v_isShared_5220_ == 0)
{
v___x_5222_ = v___x_5219_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
lean_dec(v_declName_5186_);
v_a_5225_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5193_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5193_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
v___jp_5190_:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5191_ = lean_box(0);
v___x_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5191_);
return v___x_5192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5233_, v___y_5234_, v___y_5235_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_){
_start:
{
lean_object* v___f_5242_; lean_object* v___x_5243_; 
lean_inc(v_declName_5238_);
v___f_5242_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5242_, 0, v_declName_5238_);
v___x_5243_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5238_, v___f_5242_, v_a_5239_, v_a_5240_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_){
_start:
{
lean_object* v_res_5248_; 
v_res_5248_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5244_, v_a_5245_, v_a_5246_);
lean_dec(v_a_5246_);
lean_dec_ref(v_a_5245_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5249_, uint8_t v_addHypotheses_5250_, lean_object* v_as_5251_, lean_object* v_as_x27_5252_, lean_object* v_b_5253_, lean_object* v_a_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_){
_start:
{
lean_object* v___x_5258_; 
v___x_5258_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5249_, v_addHypotheses_5250_, v_as_x27_5252_, v_b_5253_, v___y_5255_, v___y_5256_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5259_, lean_object* v_addHypotheses_5260_, lean_object* v_as_5261_, lean_object* v_as_x27_5262_, lean_object* v_b_5263_, lean_object* v_a_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
uint8_t v_addHypotheses_boxed_5268_; lean_object* v_res_5269_; 
v_addHypotheses_boxed_5268_ = lean_unbox(v_addHypotheses_5260_);
v_res_5269_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5259_, v_addHypotheses_boxed_5268_, v_as_5261_, v_as_x27_5262_, v_b_5263_, v_a_5264_, v___y_5265_, v___y_5266_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec(v_as_x27_5262_);
lean_dec(v_as_5261_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_){
_start:
{
lean_object* v___x_5274_; 
v___x_5274_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5270_, v___y_5272_);
return v___x_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5275_, v___y_5276_, v___y_5277_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5280_, lean_object* v_msg_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5281_, v___y_5282_, v___y_5283_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5286_, lean_object* v_msg_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5286_, v_msg_5287_, v___y_5288_, v___y_5289_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5292_, lean_object* v_macroStack_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5292_, v_macroStack_5293_, v___y_5295_);
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5298_, lean_object* v_macroStack_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5298_, v_macroStack_5299_, v___y_5300_, v___y_5301_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v___x_5307_; lean_object* v_env_5308_; uint8_t v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5307_ = lean_st_ref_get(v___y_5305_);
v_env_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc_ref(v_env_5308_);
lean_dec(v___x_5307_);
v___x_5309_ = l_Lean_isInductiveCore(v_env_5308_, v_declName_5304_);
v___x_5310_ = lean_box(v___x_5309_);
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5310_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5312_, v___y_5313_);
lean_dec(v___y_5313_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
lean_object* v___x_5320_; 
v___x_5320_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5316_, v___y_5318_);
return v___x_5320_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5321_, v___y_5322_, v___y_5323_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_){
_start:
{
if (v_____do__lift_5326_ == 0)
{
uint8_t v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; 
v___x_5330_ = 1;
v___x_5331_ = lean_box(v___x_5330_);
v___x_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5331_);
return v___x_5332_;
}
else
{
uint8_t v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; 
v___x_5333_ = 0;
v___x_5334_ = lean_box(v___x_5333_);
v___x_5335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5335_, 0, v___x_5334_);
return v___x_5335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
uint8_t v_____do__lift_1704__boxed_5340_; lean_object* v_res_5341_; 
v_____do__lift_1704__boxed_5340_ = lean_unbox(v_____do__lift_5336_);
v_res_5341_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1704__boxed_5340_, v___y_5337_, v___y_5338_);
lean_dec(v___y_5338_);
lean_dec_ref(v___y_5337_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5342_, size_t v_i_5343_, size_t v_stop_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
uint8_t v___x_5348_; 
v___x_5348_ = lean_usize_dec_eq(v_i_5343_, v_stop_5344_);
if (v___x_5348_ == 0)
{
uint8_t v___x_5349_; uint8_t v_a_5351_; lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5349_ = 1;
v___x_5357_ = lean_array_uget_borrowed(v_as_5342_, v_i_5343_);
lean_inc(v___x_5357_);
v___x_5358_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5357_, v___y_5346_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5368_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5361_ = v___x_5358_;
v_isShared_5362_ = v_isSharedCheck_5368_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___x_5358_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5368_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
uint8_t v___x_5363_; 
v___x_5363_ = lean_unbox(v_a_5359_);
lean_dec(v_a_5359_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; lean_object* v___x_5366_; 
v___x_5364_ = lean_box(v___x_5349_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 0, v___x_5364_);
v___x_5366_ = v___x_5361_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v___x_5364_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
else
{
lean_del_object(v___x_5361_);
v_a_5351_ = v___x_5348_;
goto v___jp_5350_;
}
}
}
else
{
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5369_; uint8_t v___x_5370_; 
v_a_5369_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5369_);
lean_dec_ref_known(v___x_5358_, 1);
v___x_5370_ = lean_unbox(v_a_5369_);
lean_dec(v_a_5369_);
v_a_5351_ = v___x_5370_;
goto v___jp_5350_;
}
else
{
return v___x_5358_;
}
}
v___jp_5350_:
{
if (v_a_5351_ == 0)
{
size_t v___x_5352_; size_t v___x_5353_; 
v___x_5352_ = ((size_t)1ULL);
v___x_5353_ = lean_usize_add(v_i_5343_, v___x_5352_);
v_i_5343_ = v___x_5353_;
goto _start;
}
else
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5355_ = lean_box(v___x_5349_);
v___x_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5355_);
return v___x_5356_;
}
}
}
else
{
uint8_t v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5371_ = 0;
v___x_5372_ = lean_box(v___x_5371_);
v___x_5373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5373_, 0, v___x_5372_);
return v___x_5373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5374_, lean_object* v_i_5375_, lean_object* v_stop_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
size_t v_i_boxed_5380_; size_t v_stop_boxed_5381_; lean_object* v_res_5382_; 
v_i_boxed_5380_ = lean_unbox_usize(v_i_5375_);
lean_dec(v_i_5375_);
v_stop_boxed_5381_ = lean_unbox_usize(v_stop_5376_);
lean_dec(v_stop_5376_);
v_res_5382_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5374_, v_i_boxed_5380_, v_stop_boxed_5381_, v___y_5377_, v___y_5378_);
lean_dec(v___y_5378_);
lean_dec_ref(v___y_5377_);
lean_dec_ref(v_as_5374_);
return v_res_5382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5383_, size_t v_i_5384_, size_t v_stop_5385_, lean_object* v_b_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
uint8_t v___x_5390_; 
v___x_5390_ = lean_usize_dec_eq(v_i_5384_, v_stop_5385_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5391_ = lean_array_uget_borrowed(v_as_5383_, v_i_5384_);
lean_inc(v___x_5391_);
v___x_5392_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5391_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v_a_5393_; size_t v___x_5394_; size_t v___x_5395_; 
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
lean_inc(v_a_5393_);
lean_dec_ref_known(v___x_5392_, 1);
v___x_5394_ = ((size_t)1ULL);
v___x_5395_ = lean_usize_add(v_i_5384_, v___x_5394_);
v_i_5384_ = v___x_5395_;
v_b_5386_ = v_a_5393_;
goto _start;
}
else
{
return v___x_5392_;
}
}
else
{
lean_object* v___x_5397_; 
v___x_5397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5397_, 0, v_b_5386_);
return v___x_5397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5398_, lean_object* v_i_5399_, lean_object* v_stop_5400_, lean_object* v_b_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
size_t v_i_boxed_5405_; size_t v_stop_boxed_5406_; lean_object* v_res_5407_; 
v_i_boxed_5405_ = lean_unbox_usize(v_i_5399_);
lean_dec(v_i_5399_);
v_stop_boxed_5406_ = lean_unbox_usize(v_stop_5400_);
lean_dec(v_stop_5400_);
v_res_5407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5398_, v_i_boxed_5405_, v_stop_boxed_5406_, v_b_5401_, v___y_5402_, v___y_5403_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec_ref(v_as_5398_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
uint8_t v___y_5413_; lean_object* v___y_5414_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___y_5450_; uint8_t v___x_5453_; 
v___x_5432_ = lean_unsigned_to_nat(0u);
v___x_5433_ = lean_array_get_size(v_declNames_5408_);
v___x_5453_ = lean_nat_dec_lt(v___x_5432_, v___x_5433_);
if (v___x_5453_ == 0)
{
lean_object* v___x_5454_; 
v___x_5454_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5453_, v_a_5409_, v_a_5410_);
v___y_5450_ = v___x_5454_;
goto v___jp_5449_;
}
else
{
if (v___x_5453_ == 0)
{
goto v___jp_5434_;
}
else
{
size_t v___x_5455_; size_t v___x_5456_; lean_object* v___x_5457_; 
v___x_5455_ = ((size_t)0ULL);
v___x_5456_ = lean_usize_of_nat(v___x_5433_);
v___x_5457_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5408_, v___x_5455_, v___x_5456_, v_a_5409_, v_a_5410_);
if (lean_obj_tag(v___x_5457_) == 0)
{
lean_object* v_a_5458_; uint8_t v___x_5459_; lean_object* v___x_5460_; 
v_a_5458_ = lean_ctor_get(v___x_5457_, 0);
lean_inc(v_a_5458_);
lean_dec_ref_known(v___x_5457_, 1);
v___x_5459_ = lean_unbox(v_a_5458_);
lean_dec(v_a_5458_);
v___x_5460_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5459_, v_a_5409_, v_a_5410_);
v___y_5450_ = v___x_5460_;
goto v___jp_5449_;
}
else
{
v___y_5450_ = v___x_5457_;
goto v___jp_5449_;
}
}
}
v___jp_5412_:
{
if (lean_obj_tag(v___y_5414_) == 0)
{
lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5422_; 
v_isSharedCheck_5422_ = !lean_is_exclusive(v___y_5414_);
if (v_isSharedCheck_5422_ == 0)
{
lean_object* v_unused_5423_; 
v_unused_5423_ = lean_ctor_get(v___y_5414_, 0);
lean_dec(v_unused_5423_);
v___x_5416_ = v___y_5414_;
v_isShared_5417_ = v_isSharedCheck_5422_;
goto v_resetjp_5415_;
}
else
{
lean_dec(v___y_5414_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5422_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
lean_object* v___x_5418_; lean_object* v___x_5420_; 
v___x_5418_ = lean_box(v___y_5413_);
if (v_isShared_5417_ == 0)
{
lean_ctor_set(v___x_5416_, 0, v___x_5418_);
v___x_5420_ = v___x_5416_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5418_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
v_a_5424_ = lean_ctor_get(v___y_5414_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___y_5414_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___y_5414_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___y_5414_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
v___jp_5434_:
{
uint8_t v___x_5435_; uint8_t v___x_5436_; 
v___x_5435_ = 1;
v___x_5436_ = lean_nat_dec_lt(v___x_5432_, v___x_5433_);
if (v___x_5436_ == 0)
{
lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5437_ = lean_box(v___x_5435_);
v___x_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5438_, 0, v___x_5437_);
return v___x_5438_;
}
else
{
lean_object* v___x_5439_; uint8_t v___x_5440_; 
v___x_5439_ = lean_box(0);
v___x_5440_ = lean_nat_dec_le(v___x_5433_, v___x_5433_);
if (v___x_5440_ == 0)
{
if (v___x_5436_ == 0)
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5441_ = lean_box(v___x_5435_);
v___x_5442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5442_, 0, v___x_5441_);
return v___x_5442_;
}
else
{
size_t v___x_5443_; size_t v___x_5444_; lean_object* v___x_5445_; 
v___x_5443_ = ((size_t)0ULL);
v___x_5444_ = lean_usize_of_nat(v___x_5433_);
v___x_5445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5408_, v___x_5443_, v___x_5444_, v___x_5439_, v_a_5409_, v_a_5410_);
v___y_5413_ = v___x_5435_;
v___y_5414_ = v___x_5445_;
goto v___jp_5412_;
}
}
else
{
size_t v___x_5446_; size_t v___x_5447_; lean_object* v___x_5448_; 
v___x_5446_ = ((size_t)0ULL);
v___x_5447_ = lean_usize_of_nat(v___x_5433_);
v___x_5448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5408_, v___x_5446_, v___x_5447_, v___x_5439_, v_a_5409_, v_a_5410_);
v___y_5413_ = v___x_5435_;
v___y_5414_ = v___x_5448_;
goto v___jp_5412_;
}
}
}
v___jp_5449_:
{
if (lean_obj_tag(v___y_5450_) == 0)
{
lean_object* v_a_5451_; uint8_t v___x_5452_; 
v_a_5451_ = lean_ctor_get(v___y_5450_, 0);
v___x_5452_ = lean_unbox(v_a_5451_);
if (v___x_5452_ == 0)
{
return v___y_5450_;
}
else
{
lean_dec_ref_known(v___y_5450_, 1);
goto v___jp_5434_;
}
}
else
{
return v___y_5450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5461_, v_a_5462_, v_a_5463_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec_ref(v_declNames_5461_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5530_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5532_ = l_Lean_Elab_registerDerivingHandler(v___x_5530_, v___x_5531_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v___x_5533_; uint8_t v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; 
lean_dec_ref_known(v___x_5532_, 1);
v___x_5533_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5534_ = 0;
v___x_5535_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5536_ = l_Lean_registerTraceClass(v___x_5533_, v___x_5534_, v___x_5535_);
return v___x_5536_;
}
else
{
return v___x_5532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5537_){
_start:
{
lean_object* v_res_5538_; 
v_res_5538_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5538_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Inhabited(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Inhabited(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Inhabited(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Inhabited(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Inhabited(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Inhabited(builtin);
}
#ifdef __cplusplus
}
#endif
