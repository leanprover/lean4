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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
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
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_runST___redArg(lean_object*);
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3_value;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "default value contains metavariables"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cannot unify"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "\nand type of constructor"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "structInstDefault"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_value),LEAN_SCALAR_PTR_LITERAL(45, 130, 215, 216, 160, 223, 59, 11)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "struct_inst_default%"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "defined "};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_94_; lean_object* v_env_95_; uint8_t v___x_96_; lean_object* v_env_97_; lean_object* v___x_98_; lean_object* v_toCold_99_; lean_object* v_mctx_100_; lean_object* v_lctx_101_; lean_object* v_options_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_94_ = lean_st_ref_get(v___y_92_);
v_env_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_env_95_);
lean_dec(v___x_94_);
v___x_96_ = 0;
v_env_97_ = l_Lean_Environment_setRecordingDeps(v_env_95_, v___x_96_);
v___x_98_ = lean_st_ref_get(v___y_90_);
v_toCold_99_ = lean_ctor_get(v___y_91_, 0);
v_mctx_100_ = lean_ctor_get(v___x_98_, 0);
lean_inc_ref(v_mctx_100_);
lean_dec(v___x_98_);
v_lctx_101_ = lean_ctor_get(v___y_89_, 2);
v_options_102_ = lean_ctor_get(v_toCold_99_, 2);
lean_inc_ref(v_options_102_);
lean_inc_ref(v_lctx_101_);
v___x_103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_103_, 0, v_env_97_);
lean_ctor_set(v___x_103_, 1, v_mctx_100_);
lean_ctor_set(v___x_103_, 2, v_lctx_101_);
lean_ctor_set(v___x_103_, 3, v_options_102_);
v___x_104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_msgData_88_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msgData_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_113_; double v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_float_of_nat(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(lean_object* v_cls_118_, lean_object* v_msg_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_ref_125_; lean_object* v___x_126_; lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_172_; 
v_ref_125_ = lean_ctor_get(v___y_122_, 2);
v___x_126_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_172_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_172_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_172_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v_traceState_132_; lean_object* v_env_133_; lean_object* v_nextMacroScope_134_; lean_object* v_ngen_135_; lean_object* v_auxDeclNGen_136_; lean_object* v_cache_137_; lean_object* v_recordedDeps_138_; lean_object* v_messages_139_; lean_object* v_infoState_140_; lean_object* v_snapshotTasks_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_171_; 
v___x_131_ = lean_st_ref_take(v___y_123_);
v_traceState_132_ = lean_ctor_get(v___x_131_, 4);
v_env_133_ = lean_ctor_get(v___x_131_, 0);
v_nextMacroScope_134_ = lean_ctor_get(v___x_131_, 1);
v_ngen_135_ = lean_ctor_get(v___x_131_, 2);
v_auxDeclNGen_136_ = lean_ctor_get(v___x_131_, 3);
v_cache_137_ = lean_ctor_get(v___x_131_, 5);
v_recordedDeps_138_ = lean_ctor_get(v___x_131_, 6);
v_messages_139_ = lean_ctor_get(v___x_131_, 7);
v_infoState_140_ = lean_ctor_get(v___x_131_, 8);
v_snapshotTasks_141_ = lean_ctor_get(v___x_131_, 9);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_171_ == 0)
{
v___x_143_ = v___x_131_;
v_isShared_144_ = v_isSharedCheck_171_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_snapshotTasks_141_);
lean_inc(v_infoState_140_);
lean_inc(v_messages_139_);
lean_inc(v_recordedDeps_138_);
lean_inc(v_cache_137_);
lean_inc(v_traceState_132_);
lean_inc(v_auxDeclNGen_136_);
lean_inc(v_ngen_135_);
lean_inc(v_nextMacroScope_134_);
lean_inc(v_env_133_);
lean_dec(v___x_131_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_171_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
uint64_t v_tid_145_; lean_object* v_traces_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_170_; 
v_tid_145_ = lean_ctor_get_uint64(v_traceState_132_, sizeof(void*)*1);
v_traces_146_ = lean_ctor_get(v_traceState_132_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_traceState_132_);
if (v_isSharedCheck_170_ == 0)
{
v___x_148_ = v_traceState_132_;
v_isShared_149_ = v_isSharedCheck_170_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_traces_146_);
lean_dec(v_traceState_132_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_170_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; double v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_150_ = lean_box(0);
v___x_151_ = lean_box(0);
v___x_152_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
v___x_153_ = 0;
v___x_154_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_155_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_155_, 0, v_cls_118_);
lean_ctor_set(v___x_155_, 1, v___x_151_);
lean_ctor_set(v___x_155_, 2, v___x_154_);
lean_ctor_set_float(v___x_155_, sizeof(void*)*3, v___x_152_);
lean_ctor_set_float(v___x_155_, sizeof(void*)*3 + 8, v___x_152_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*3 + 16, v___x_153_);
v___x_156_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__2));
v___x_157_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v_a_127_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_inc(v_ref_125_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_ref_125_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = l_Lean_PersistentArray_push___redArg(v_traces_146_, v___x_158_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_159_);
v___x_161_ = v___x_148_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_159_);
lean_ctor_set_uint64(v_reuseFailAlloc_169_, sizeof(void*)*1, v_tid_145_);
v___x_161_ = v_reuseFailAlloc_169_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_163_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 4, v___x_161_);
v___x_163_ = v___x_143_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_env_133_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_nextMacroScope_134_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_ngen_135_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_auxDeclNGen_136_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_168_, 5, v_cache_137_);
lean_ctor_set(v_reuseFailAlloc_168_, 6, v_recordedDeps_138_);
lean_ctor_set(v_reuseFailAlloc_168_, 7, v_messages_139_);
lean_ctor_set(v_reuseFailAlloc_168_, 8, v_infoState_140_);
lean_ctor_set(v_reuseFailAlloc_168_, 9, v_snapshotTasks_141_);
v___x_163_ = v_reuseFailAlloc_168_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_st_ref_put(v___y_123_, v___x_163_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_150_);
v___x_166_ = v___x_129_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_150_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___boxed(lean_object* v_cls_173_, lean_object* v_msg_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_173_, v_msg_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_192_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
v___x_193_ = l_Lean_Name_append(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__7));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed(lean_object* v_a_200_, lean_object* v___x_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_k_204_, lean_object* v_tail_205_, lean_object* v_a_206_, lean_object* v_inst_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(v_a_200_, v___x_201_, v_a_202_, v_a_203_, v_k_204_, v_tail_205_, v_a_206_, v_inst_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___x_201_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(lean_object* v_k_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
if (lean_obj_tag(v_a_220_) == 0)
{
lean_object* v___x_231_; 
lean_dec(v_a_221_);
lean_inc(v_a_229_);
lean_inc_ref(v_a_228_);
lean_inc(v_a_227_);
lean_inc_ref(v_a_226_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_224_);
v___x_231_ = lean_apply_9(v_k_219_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, lean_box(0));
return v___x_231_;
}
else
{
lean_object* v_head_232_; lean_object* v_tail_233_; lean_object* v___y_235_; lean_object* v_a_236_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_head_232_ = lean_ctor_get(v_a_220_, 0);
lean_inc(v_head_232_);
v_tail_233_ = lean_ctor_get(v_a_220_, 1);
lean_inc(v_tail_233_);
lean_dec_ref_known(v_a_220_, 2);
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_mk_empty_array_with_capacity(v___x_243_);
v___x_245_ = lean_array_push(v___x_244_, v_head_232_);
v___x_246_ = l_Lean_Meta_mkAppM(v___x_242_, v___x_245_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___f_248_; uint8_t v___x_249_; lean_object* v___x_250_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_n(v_a_247_, 3);
lean_dec_ref_known(v___x_246_, 1);
lean_inc(v_tail_233_);
lean_inc_ref(v_k_219_);
lean_inc(v_a_223_);
lean_inc_ref(v_a_222_);
lean_inc(v_a_221_);
v___f_248_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed), 15, 7);
lean_closure_set(v___f_248_, 0, v_a_221_);
lean_closure_set(v___f_248_, 1, v___x_243_);
lean_closure_set(v___f_248_, 2, v_a_222_);
lean_closure_set(v___f_248_, 3, v_a_223_);
lean_closure_set(v___f_248_, 4, v_k_219_);
lean_closure_set(v___f_248_, 5, v_tail_233_);
lean_closure_set(v___f_248_, 6, v_a_247_);
v___x_249_ = 0;
v___x_250_ = l_Lean_Meta_check(v_a_247_, v___x_249_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref_known(v___x_250_, 1);
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3));
v___x_252_ = l_Lean_Core_mkFreshUserName(v___x_251_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; uint8_t v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
v___x_254_ = 3;
v___x_255_ = 0;
v___x_256_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_a_253_, v___x_254_, v_a_247_, v___f_248_, v___x_255_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_dec(v_tail_233_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_k_219_);
return v___x_256_;
}
else
{
lean_object* v_a_257_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
v___y_235_ = v___x_256_;
v_a_236_ = v_a_257_;
goto v___jp_234_;
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v___f_248_);
lean_dec(v_a_247_);
v_a_258_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_252_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_252_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
lean_inc(v_a_258_);
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
v___y_235_ = v___x_263_;
v_a_236_ = v_a_258_;
goto v___jp_234_;
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v___f_248_);
lean_dec(v_a_247_);
v_a_266_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_250_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_250_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
lean_inc(v_a_266_);
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v___y_235_ = v___x_271_;
v_a_236_ = v_a_266_;
goto v___jp_234_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_246_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_246_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
lean_inc(v_a_274_);
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
v___y_235_ = v___x_279_;
v_a_236_ = v_a_274_;
goto v___jp_234_;
}
}
}
v___jp_234_:
{
uint8_t v___x_237_; 
v___x_237_ = l_Lean_Exception_isInterrupt(v_a_236_);
if (v___x_237_ == 0)
{
uint8_t v___x_238_; 
v___x_238_ = l_Lean_Exception_isRuntime(v_a_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v___y_235_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_a_221_, v___x_239_);
lean_dec(v_a_221_);
v_a_220_ = v_tail_233_;
v_a_221_ = v___x_240_;
goto _start;
}
else
{
lean_dec(v_tail_233_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_k_219_);
return v___y_235_;
}
}
else
{
lean_dec_ref(v_a_236_);
lean_dec(v_tail_233_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_k_219_);
return v___y_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(lean_object* v_a_282_, lean_object* v___x_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_k_286_, lean_object* v_tail_287_, lean_object* v_a_288_, lean_object* v_inst_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v_toCold_309_; lean_object* v_options_310_; uint8_t v_hasTrace_311_; 
v_toCold_309_ = lean_ctor_get(v___y_294_, 0);
v_options_310_ = lean_ctor_get(v_toCold_309_, 2);
v_hasTrace_311_ = lean_ctor_get_uint8(v_options_310_, sizeof(void*)*1);
if (v_hasTrace_311_ == 0)
{
lean_dec_ref(v_a_288_);
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
v___y_302_ = v___y_294_;
v___y_303_ = v___y_295_;
goto v___jp_297_;
}
else
{
lean_object* v_inheritedTraceOptions_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_inheritedTraceOptions_312_ = lean_ctor_get(v_toCold_309_, 11);
v___x_313_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_314_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_315_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_312_, v_options_310_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_a_288_);
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
v___y_302_ = v___y_294_;
v___y_303_ = v___y_295_;
goto v___jp_297_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8);
v___x_317_ = l_Lean_MessageData_ofExpr(v_a_288_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_313_, v___x_318_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_dec_ref_known(v___x_319_, 1);
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
v___y_302_ = v___y_294_;
v___y_303_ = v___y_295_;
goto v___jp_297_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_inst_289_);
lean_dec(v_tail_287_);
lean_dec_ref(v_k_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_282_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
v___jp_297_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_304_ = lean_nat_add(v_a_282_, v___x_283_);
lean_inc_ref(v_inst_289_);
v___x_305_ = lean_array_push(v_a_284_, v_inst_289_);
v___x_306_ = l_Lean_Expr_fvarId_x21(v_inst_289_);
lean_dec_ref(v_inst_289_);
v___x_307_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_306_, v_a_282_, v_a_285_);
v___x_308_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_286_, v_tail_287_, v___x_304_, v___x_305_, v___x_307_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___boxed(lean_object* v_k_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(lean_object* v_00_u03b1_341_, lean_object* v_k_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___boxed(lean_object* v_00_u03b1_355_, lean_object* v_k_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(v_00_u03b1_355_, v_k_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(lean_object* v_cls_369_, lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_369_, v_msg_370_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___boxed(lean_object* v_cls_379_, lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(v_cls_379_, v_msg_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(uint8_t v_addHypotheses_391_, lean_object* v_xs_392_, lean_object* v_k_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
if (v_addHypotheses_391_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v_xs_392_);
v___x_401_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_402_ = lean_box(1);
lean_inc(v_a_399_);
lean_inc_ref(v_a_398_);
lean_inc(v_a_397_);
lean_inc_ref(v_a_396_);
lean_inc(v_a_395_);
lean_inc_ref(v_a_394_);
v___x_403_ = lean_apply_9(v_k_393_, v___x_401_, v___x_402_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, lean_box(0));
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_404_ = lean_array_to_list(v_xs_392_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_407_ = lean_box(1);
v___x_408_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_393_, v___x_404_, v___x_405_, v___x_406_, v___x_407_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___boxed(lean_object* v_addHypotheses_409_, lean_object* v_xs_410_, lean_object* v_k_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
uint8_t v_addHypotheses_boxed_419_; lean_object* v_res_420_; 
v_addHypotheses_boxed_419_ = lean_unbox(v_addHypotheses_409_);
v_res_420_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_boxed_419_, v_xs_410_, v_k_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(uint8_t v_addHypotheses_421_, lean_object* v_00_u03b1_422_, lean_object* v_xs_423_, lean_object* v_k_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_421_, v_xs_423_, v_k_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed(lean_object* v_addHypotheses_433_, lean_object* v_00_u03b1_434_, lean_object* v_xs_435_, lean_object* v_k_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
uint8_t v_addHypotheses_boxed_444_; lean_object* v_res_445_; 
v_addHypotheses_boxed_444_ = lean_unbox(v_addHypotheses_433_);
v_res_445_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(v_addHypotheses_boxed_444_, v_00_u03b1_434_, v_xs_435_, v_k_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(lean_object* v_k_446_, lean_object* v_v_447_, lean_object* v_t_448_){
_start:
{
if (lean_obj_tag(v_t_448_) == 0)
{
lean_object* v_size_449_; lean_object* v_k_450_; lean_object* v_v_451_; lean_object* v_l_452_; lean_object* v_r_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_734_; 
v_size_449_ = lean_ctor_get(v_t_448_, 0);
v_k_450_ = lean_ctor_get(v_t_448_, 1);
v_v_451_ = lean_ctor_get(v_t_448_, 2);
v_l_452_ = lean_ctor_get(v_t_448_, 3);
v_r_453_ = lean_ctor_get(v_t_448_, 4);
v_isSharedCheck_734_ = !lean_is_exclusive(v_t_448_);
if (v_isSharedCheck_734_ == 0)
{
v___x_455_ = v_t_448_;
v_isShared_456_ = v_isSharedCheck_734_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_r_453_);
lean_inc(v_l_452_);
lean_inc(v_v_451_);
lean_inc(v_k_450_);
lean_inc(v_size_449_);
lean_dec(v_t_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_734_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
uint8_t v___x_457_; 
v___x_457_ = lean_nat_dec_lt(v_k_446_, v_k_450_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = lean_nat_dec_eq(v_k_446_, v_k_450_);
if (v___x_458_ == 0)
{
lean_object* v_impl_459_; lean_object* v___x_460_; 
lean_dec(v_size_449_);
v_impl_459_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_446_, v_v_447_, v_r_453_);
v___x_460_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_452_) == 0)
{
lean_object* v_size_461_; lean_object* v_size_462_; lean_object* v_k_463_; lean_object* v_v_464_; lean_object* v_l_465_; lean_object* v_r_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_size_461_ = lean_ctor_get(v_l_452_, 0);
v_size_462_ = lean_ctor_get(v_impl_459_, 0);
v_k_463_ = lean_ctor_get(v_impl_459_, 1);
v_v_464_ = lean_ctor_get(v_impl_459_, 2);
v_l_465_ = lean_ctor_get(v_impl_459_, 3);
lean_inc(v_l_465_);
v_r_466_ = lean_ctor_get(v_impl_459_, 4);
v___x_467_ = lean_unsigned_to_nat(3u);
v___x_468_ = lean_nat_mul(v___x_467_, v_size_461_);
v___x_469_ = lean_nat_dec_lt(v___x_468_, v_size_462_);
lean_dec(v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
lean_dec(v_l_465_);
v___x_470_ = lean_nat_add(v___x_460_, v_size_461_);
v___x_471_ = lean_nat_add(v___x_470_, v_size_462_);
lean_dec(v___x_470_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_impl_459_);
lean_ctor_set(v___x_455_, 0, v___x_471_);
v___x_473_ = v___x_455_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_impl_459_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
else
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_538_; 
lean_inc(v_r_466_);
lean_inc(v_v_464_);
lean_inc(v_k_463_);
lean_inc(v_size_462_);
v_isSharedCheck_538_ = !lean_is_exclusive(v_impl_459_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_539_ = lean_ctor_get(v_impl_459_, 4);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_impl_459_, 3);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_impl_459_, 2);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_impl_459_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_impl_459_, 0);
lean_dec(v_unused_543_);
v___x_476_ = v_impl_459_;
v_isShared_477_ = v_isSharedCheck_538_;
goto v_resetjp_475_;
}
else
{
lean_dec(v_impl_459_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_538_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_size_478_; lean_object* v_k_479_; lean_object* v_v_480_; lean_object* v_l_481_; lean_object* v_r_482_; lean_object* v_size_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_size_478_ = lean_ctor_get(v_l_465_, 0);
v_k_479_ = lean_ctor_get(v_l_465_, 1);
v_v_480_ = lean_ctor_get(v_l_465_, 2);
v_l_481_ = lean_ctor_get(v_l_465_, 3);
v_r_482_ = lean_ctor_get(v_l_465_, 4);
v_size_483_ = lean_ctor_get(v_r_466_, 0);
v___x_484_ = lean_unsigned_to_nat(2u);
v___x_485_ = lean_nat_mul(v___x_484_, v_size_483_);
v___x_486_ = lean_nat_dec_lt(v_size_478_, v___x_485_);
lean_dec(v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_514_; 
lean_inc(v_r_482_);
lean_inc(v_l_481_);
lean_inc(v_v_480_);
lean_inc(v_k_479_);
v_isSharedCheck_514_ = !lean_is_exclusive(v_l_465_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; lean_object* v_unused_518_; lean_object* v_unused_519_; 
v_unused_515_ = lean_ctor_get(v_l_465_, 4);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_l_465_, 3);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_l_465_, 2);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_l_465_, 1);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_l_465_, 0);
lean_dec(v_unused_519_);
v___x_488_ = v_l_465_;
v_isShared_489_ = v_isSharedCheck_514_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_l_465_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_514_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_504_; 
v___x_490_ = lean_nat_add(v___x_460_, v_size_461_);
v___x_491_ = lean_nat_add(v___x_490_, v_size_462_);
lean_dec(v_size_462_);
if (lean_obj_tag(v_l_481_) == 0)
{
lean_object* v_size_512_; 
v_size_512_ = lean_ctor_get(v_l_481_, 0);
lean_inc(v_size_512_);
v___y_504_ = v_size_512_;
goto v___jp_503_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___y_504_ = v___x_513_;
goto v___jp_503_;
}
v___jp_492_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_nat_add(v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec(v___y_494_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_r_466_);
lean_ctor_set(v___x_488_, 3, v_r_482_);
lean_ctor_set(v___x_488_, 2, v_v_464_);
lean_ctor_set(v___x_488_, 1, v_k_463_);
lean_ctor_set(v___x_488_, 0, v___x_496_);
v___x_498_ = v___x_488_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_k_463_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_v_464_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_r_482_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_r_466_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_498_);
lean_ctor_set(v___x_476_, 3, v___y_493_);
lean_ctor_set(v___x_476_, 2, v_v_480_);
lean_ctor_set(v___x_476_, 1, v_k_479_);
lean_ctor_set(v___x_476_, 0, v___x_491_);
v___x_500_ = v___x_476_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_k_479_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_v_480_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v___y_493_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_nat_add(v___x_490_, v___y_504_);
lean_dec(v___y_504_);
lean_dec(v___x_490_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_l_481_);
lean_ctor_set(v___x_455_, 0, v___x_505_);
v___x_507_ = v___x_455_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_l_481_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_nat_add(v___x_460_, v_size_483_);
if (lean_obj_tag(v_r_482_) == 0)
{
lean_object* v_size_509_; 
v_size_509_ = lean_ctor_get(v_r_482_, 0);
lean_inc(v_size_509_);
v___y_493_ = v___x_507_;
v___y_494_ = v___x_508_;
v___y_495_ = v_size_509_;
goto v___jp_492_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___y_493_ = v___x_507_;
v___y_494_ = v___x_508_;
v___y_495_ = v___x_510_;
goto v___jp_492_;
}
}
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
lean_del_object(v___x_455_);
v___x_520_ = lean_nat_add(v___x_460_, v_size_461_);
v___x_521_ = lean_nat_add(v___x_520_, v_size_462_);
lean_dec(v_size_462_);
v___x_522_ = lean_nat_add(v___x_520_, v_size_478_);
lean_dec(v___x_520_);
lean_inc_ref(v_l_452_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_l_465_);
lean_ctor_set(v___x_476_, 3, v_l_452_);
lean_ctor_set(v___x_476_, 2, v_v_451_);
lean_ctor_set(v___x_476_, 1, v_k_450_);
lean_ctor_set(v___x_476_, 0, v___x_522_);
v___x_524_ = v___x_476_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_537_, 4, v_l_465_);
v___x_524_ = v_reuseFailAlloc_537_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_isSharedCheck_531_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; lean_object* v_unused_533_; lean_object* v_unused_534_; lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_532_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_l_452_, 2);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_l_452_, 1);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_536_);
v___x_526_ = v_l_452_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_l_452_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v_r_466_);
lean_ctor_set(v___x_526_, 3, v___x_524_);
lean_ctor_set(v___x_526_, 2, v_v_464_);
lean_ctor_set(v___x_526_, 1, v_k_463_);
lean_ctor_set(v___x_526_, 0, v___x_521_);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_k_463_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_v_464_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v_r_466_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_544_; 
v_l_544_ = lean_ctor_get(v_impl_459_, 3);
lean_inc(v_l_544_);
if (lean_obj_tag(v_l_544_) == 0)
{
lean_object* v_r_545_; lean_object* v_k_546_; lean_object* v_v_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_570_; 
v_r_545_ = lean_ctor_get(v_impl_459_, 4);
v_k_546_ = lean_ctor_get(v_impl_459_, 1);
v_v_547_ = lean_ctor_get(v_impl_459_, 2);
v_isSharedCheck_570_ = !lean_is_exclusive(v_impl_459_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; 
v_unused_571_ = lean_ctor_get(v_impl_459_, 3);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_impl_459_, 0);
lean_dec(v_unused_572_);
v___x_549_ = v_impl_459_;
v_isShared_550_ = v_isSharedCheck_570_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_r_545_);
lean_inc(v_v_547_);
lean_inc(v_k_546_);
lean_dec(v_impl_459_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_570_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v_k_551_; lean_object* v_v_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_566_; 
v_k_551_ = lean_ctor_get(v_l_544_, 1);
v_v_552_ = lean_ctor_get(v_l_544_, 2);
v_isSharedCheck_566_ = !lean_is_exclusive(v_l_544_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_567_ = lean_ctor_get(v_l_544_, 4);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_l_544_, 3);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_l_544_, 0);
lean_dec(v_unused_569_);
v___x_554_ = v_l_544_;
v_isShared_555_ = v_isSharedCheck_566_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_v_552_);
lean_inc(v_k_551_);
lean_dec(v_l_544_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_566_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_545_, 2);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 4, v_r_545_);
lean_ctor_set(v___x_554_, 3, v_r_545_);
lean_ctor_set(v___x_554_, 2, v_v_451_);
lean_ctor_set(v___x_554_, 1, v_k_450_);
lean_ctor_set(v___x_554_, 0, v___x_460_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_r_545_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_r_545_);
v___x_558_ = v_reuseFailAlloc_565_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
lean_inc(v_r_545_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 3, v_r_545_);
lean_ctor_set(v___x_549_, 0, v___x_460_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_k_546_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_v_547_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_r_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_r_545_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_560_);
lean_ctor_set(v___x_455_, 3, v___x_558_);
lean_ctor_set(v___x_455_, 2, v_v_552_);
lean_ctor_set(v___x_455_, 1, v_k_551_);
lean_ctor_set(v___x_455_, 0, v___x_556_);
v___x_562_ = v___x_455_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_k_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_v_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v___x_560_);
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
}
}
else
{
lean_object* v_r_573_; 
v_r_573_ = lean_ctor_get(v_impl_459_, 4);
lean_inc(v_r_573_);
if (lean_obj_tag(v_r_573_) == 0)
{
lean_object* v_k_574_; lean_object* v_v_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_586_; 
v_k_574_ = lean_ctor_get(v_impl_459_, 1);
v_v_575_ = lean_ctor_get(v_impl_459_, 2);
v_isSharedCheck_586_ = !lean_is_exclusive(v_impl_459_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; lean_object* v_unused_588_; lean_object* v_unused_589_; 
v_unused_587_ = lean_ctor_get(v_impl_459_, 4);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_impl_459_, 3);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_impl_459_, 0);
lean_dec(v_unused_589_);
v___x_577_ = v_impl_459_;
v_isShared_578_ = v_isSharedCheck_586_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_v_575_);
lean_inc(v_k_574_);
lean_dec(v_impl_459_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_586_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(3u);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 4, v_l_544_);
lean_ctor_set(v___x_577_, 2, v_v_451_);
lean_ctor_set(v___x_577_, 1, v_k_450_);
lean_ctor_set(v___x_577_, 0, v___x_460_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_l_544_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_l_544_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_r_573_);
lean_ctor_set(v___x_455_, 3, v___x_581_);
lean_ctor_set(v___x_455_, 2, v_v_575_);
lean_ctor_set(v___x_455_, 1, v_k_574_);
lean_ctor_set(v___x_455_, 0, v___x_579_);
v___x_583_ = v___x_455_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_k_574_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_v_575_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_r_573_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(2u);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_impl_459_);
lean_ctor_set(v___x_455_, 3, v_r_573_);
lean_ctor_set(v___x_455_, 0, v___x_590_);
v___x_592_ = v___x_455_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_r_573_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_impl_459_);
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
else
{
lean_object* v___x_595_; 
lean_dec(v_v_451_);
lean_dec(v_k_450_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 2, v_v_447_);
lean_ctor_set(v___x_455_, 1, v_k_446_);
v___x_595_ = v___x_455_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_size_449_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_k_446_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_v_447_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_r_453_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_impl_597_; lean_object* v___x_598_; 
lean_dec(v_size_449_);
v_impl_597_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_446_, v_v_447_, v_l_452_);
v___x_598_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_453_) == 0)
{
lean_object* v_size_599_; lean_object* v_size_600_; lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v_l_603_; lean_object* v_r_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_size_599_ = lean_ctor_get(v_r_453_, 0);
v_size_600_ = lean_ctor_get(v_impl_597_, 0);
v_k_601_ = lean_ctor_get(v_impl_597_, 1);
v_v_602_ = lean_ctor_get(v_impl_597_, 2);
v_l_603_ = lean_ctor_get(v_impl_597_, 3);
v_r_604_ = lean_ctor_get(v_impl_597_, 4);
lean_inc(v_r_604_);
v___x_605_ = lean_unsigned_to_nat(3u);
v___x_606_ = lean_nat_mul(v___x_605_, v_size_599_);
v___x_607_ = lean_nat_dec_lt(v___x_606_, v_size_600_);
lean_dec(v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec(v_r_604_);
v___x_608_ = lean_nat_add(v___x_598_, v_size_600_);
v___x_609_ = lean_nat_add(v___x_608_, v_size_599_);
lean_dec(v___x_608_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 3, v_impl_597_);
lean_ctor_set(v___x_455_, 0, v___x_609_);
v___x_611_ = v___x_455_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_impl_597_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_r_453_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
else
{
lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_l_603_);
lean_inc(v_v_602_);
lean_inc(v_k_601_);
lean_inc(v_size_600_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_impl_597_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; 
v_unused_679_ = lean_ctor_get(v_impl_597_, 4);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_impl_597_, 3);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_impl_597_, 2);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_impl_597_, 1);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_impl_597_, 0);
lean_dec(v_unused_683_);
v___x_614_ = v_impl_597_;
v_isShared_615_ = v_isSharedCheck_678_;
goto v_resetjp_613_;
}
else
{
lean_dec(v_impl_597_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_678_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_size_616_; lean_object* v_size_617_; lean_object* v_k_618_; lean_object* v_v_619_; lean_object* v_l_620_; lean_object* v_r_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_size_616_ = lean_ctor_get(v_l_603_, 0);
v_size_617_ = lean_ctor_get(v_r_604_, 0);
v_k_618_ = lean_ctor_get(v_r_604_, 1);
v_v_619_ = lean_ctor_get(v_r_604_, 2);
v_l_620_ = lean_ctor_get(v_r_604_, 3);
v_r_621_ = lean_ctor_get(v_r_604_, 4);
v___x_622_ = lean_unsigned_to_nat(2u);
v___x_623_ = lean_nat_mul(v___x_622_, v_size_616_);
v___x_624_ = lean_nat_dec_lt(v_size_617_, v___x_623_);
lean_dec(v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_653_; 
lean_inc(v_r_621_);
lean_inc(v_l_620_);
lean_inc(v_v_619_);
lean_inc(v_k_618_);
v_isSharedCheck_653_ = !lean_is_exclusive(v_r_604_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; lean_object* v_unused_658_; 
v_unused_654_ = lean_ctor_get(v_r_604_, 4);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_r_604_, 3);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_r_604_, 2);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_r_604_, 1);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_r_604_, 0);
lean_dec(v_unused_658_);
v___x_626_ = v_r_604_;
v_isShared_627_ = v_isSharedCheck_653_;
goto v_resetjp_625_;
}
else
{
lean_dec(v_r_604_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_653_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___x_641_; lean_object* v___y_643_; 
v___x_628_ = lean_nat_add(v___x_598_, v_size_600_);
lean_dec(v_size_600_);
v___x_629_ = lean_nat_add(v___x_628_, v_size_599_);
lean_dec(v___x_628_);
v___x_641_ = lean_nat_add(v___x_598_, v_size_616_);
if (lean_obj_tag(v_l_620_) == 0)
{
lean_object* v_size_651_; 
v_size_651_ = lean_ctor_get(v_l_620_, 0);
lean_inc(v_size_651_);
v___y_643_ = v_size_651_;
goto v___jp_642_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___y_643_ = v___x_652_;
goto v___jp_642_;
}
v___jp_630_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_nat_add(v___y_631_, v___y_633_);
lean_dec(v___y_633_);
lean_dec(v___y_631_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_r_453_);
lean_ctor_set(v___x_626_, 3, v_r_621_);
lean_ctor_set(v___x_626_, 2, v_v_451_);
lean_ctor_set(v___x_626_, 1, v_k_450_);
lean_ctor_set(v___x_626_, 0, v___x_634_);
v___x_636_ = v___x_626_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_r_621_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v_r_453_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 4, v___x_636_);
lean_ctor_set(v___x_614_, 3, v___y_632_);
lean_ctor_set(v___x_614_, 2, v_v_619_);
lean_ctor_set(v___x_614_, 1, v_k_618_);
lean_ctor_set(v___x_614_, 0, v___x_629_);
v___x_638_ = v___x_614_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_618_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_619_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v___y_632_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_nat_add(v___x_641_, v___y_643_);
lean_dec(v___y_643_);
lean_dec(v___x_641_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_l_620_);
lean_ctor_set(v___x_455_, 3, v_l_603_);
lean_ctor_set(v___x_455_, 2, v_v_602_);
lean_ctor_set(v___x_455_, 1, v_k_601_);
lean_ctor_set(v___x_455_, 0, v___x_644_);
v___x_646_ = v___x_455_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_k_601_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_v_602_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_l_603_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_l_620_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; 
v___x_647_ = lean_nat_add(v___x_598_, v_size_599_);
if (lean_obj_tag(v_r_621_) == 0)
{
lean_object* v_size_648_; 
v_size_648_ = lean_ctor_get(v_r_621_, 0);
lean_inc(v_size_648_);
v___y_631_ = v___x_647_;
v___y_632_ = v___x_646_;
v___y_633_ = v_size_648_;
goto v___jp_630_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___y_631_ = v___x_647_;
v___y_632_ = v___x_646_;
v___y_633_ = v___x_649_;
goto v___jp_630_;
}
}
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_del_object(v___x_455_);
v___x_659_ = lean_nat_add(v___x_598_, v_size_600_);
lean_dec(v_size_600_);
v___x_660_ = lean_nat_add(v___x_659_, v_size_599_);
lean_dec(v___x_659_);
v___x_661_ = lean_nat_add(v___x_598_, v_size_599_);
v___x_662_ = lean_nat_add(v___x_661_, v_size_617_);
lean_dec(v___x_661_);
lean_inc_ref(v_r_453_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 4, v_r_453_);
lean_ctor_set(v___x_614_, 3, v_r_604_);
lean_ctor_set(v___x_614_, 2, v_v_451_);
lean_ctor_set(v___x_614_, 1, v_k_450_);
lean_ctor_set(v___x_614_, 0, v___x_662_);
v___x_664_ = v___x_614_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_r_604_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_r_453_);
v___x_664_ = v_reuseFailAlloc_677_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_isSharedCheck_671_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; lean_object* v_unused_673_; lean_object* v_unused_674_; lean_object* v_unused_675_; lean_object* v_unused_676_; 
v_unused_672_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_r_453_, 2);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_r_453_, 1);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_r_453_, 0);
lean_dec(v_unused_676_);
v___x_666_ = v_r_453_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_r_453_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v___x_664_);
lean_ctor_set(v___x_666_, 3, v_l_603_);
lean_ctor_set(v___x_666_, 2, v_v_602_);
lean_ctor_set(v___x_666_, 1, v_k_601_);
lean_ctor_set(v___x_666_, 0, v___x_660_);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_k_601_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_v_602_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_l_603_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v___x_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_684_; 
v_l_684_ = lean_ctor_get(v_impl_597_, 3);
if (lean_obj_tag(v_l_684_) == 0)
{
lean_object* v_r_685_; lean_object* v_k_686_; lean_object* v_v_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_698_; 
lean_inc_ref(v_l_684_);
v_r_685_ = lean_ctor_get(v_impl_597_, 4);
v_k_686_ = lean_ctor_get(v_impl_597_, 1);
v_v_687_ = lean_ctor_get(v_impl_597_, 2);
v_isSharedCheck_698_ = !lean_is_exclusive(v_impl_597_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_699_ = lean_ctor_get(v_impl_597_, 3);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_impl_597_, 0);
lean_dec(v_unused_700_);
v___x_689_ = v_impl_597_;
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_r_685_);
lean_inc(v_v_687_);
lean_inc(v_k_686_);
lean_dec(v_impl_597_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_685_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 3, v_r_685_);
lean_ctor_set(v___x_689_, 2, v_v_451_);
lean_ctor_set(v___x_689_, 1, v_k_450_);
lean_ctor_set(v___x_689_, 0, v___x_598_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_r_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_r_685_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_693_);
lean_ctor_set(v___x_455_, 3, v_l_684_);
lean_ctor_set(v___x_455_, 2, v_v_687_);
lean_ctor_set(v___x_455_, 1, v_k_686_);
lean_ctor_set(v___x_455_, 0, v___x_691_);
v___x_695_ = v___x_455_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_k_686_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_v_687_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_l_684_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_r_701_; 
v_r_701_ = lean_ctor_get(v_impl_597_, 4);
lean_inc(v_r_701_);
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v_k_702_; lean_object* v_v_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_726_; 
lean_inc(v_l_684_);
v_k_702_ = lean_ctor_get(v_impl_597_, 1);
v_v_703_ = lean_ctor_get(v_impl_597_, 2);
v_isSharedCheck_726_ = !lean_is_exclusive(v_impl_597_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; lean_object* v_unused_728_; lean_object* v_unused_729_; 
v_unused_727_ = lean_ctor_get(v_impl_597_, 4);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_impl_597_, 3);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_impl_597_, 0);
lean_dec(v_unused_729_);
v___x_705_ = v_impl_597_;
v_isShared_706_ = v_isSharedCheck_726_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_v_703_);
lean_inc(v_k_702_);
lean_dec(v_impl_597_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_726_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_722_; 
v_k_707_ = lean_ctor_get(v_r_701_, 1);
v_v_708_ = lean_ctor_get(v_r_701_, 2);
v_isSharedCheck_722_ = !lean_is_exclusive(v_r_701_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; 
v_unused_723_ = lean_ctor_get(v_r_701_, 4);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_r_701_, 3);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_r_701_, 0);
lean_dec(v_unused_725_);
v___x_710_ = v_r_701_;
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_v_708_);
lean_inc(v_k_707_);
lean_dec(v_r_701_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_unsigned_to_nat(3u);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_l_684_);
lean_ctor_set(v___x_710_, 3, v_l_684_);
lean_ctor_set(v___x_710_, 2, v_v_703_);
lean_ctor_set(v___x_710_, 1, v_k_702_);
lean_ctor_set(v___x_710_, 0, v___x_598_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_k_702_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_v_703_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_l_684_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_l_684_);
v___x_714_ = v_reuseFailAlloc_721_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_l_684_);
lean_ctor_set(v___x_705_, 2, v_v_451_);
lean_ctor_set(v___x_705_, 1, v_k_450_);
lean_ctor_set(v___x_705_, 0, v___x_598_);
v___x_716_ = v___x_705_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_l_684_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_l_684_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_716_);
lean_ctor_set(v___x_455_, 3, v___x_714_);
lean_ctor_set(v___x_455_, 2, v_v_708_);
lean_ctor_set(v___x_455_, 1, v_k_707_);
lean_ctor_set(v___x_455_, 0, v___x_712_);
v___x_718_ = v___x_455_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_unsigned_to_nat(2u);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_r_701_);
lean_ctor_set(v___x_455_, 3, v_impl_597_);
lean_ctor_set(v___x_455_, 0, v___x_730_);
v___x_732_ = v___x_455_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_impl_597_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_r_701_);
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
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_k_446_);
lean_ctor_set(v___x_736_, 2, v_v_447_);
lean_ctor_set(v___x_736_, 3, v_t_448_);
lean_ctor_set(v___x_736_, 4, v_t_448_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(lean_object* v_t_737_, lean_object* v_k_738_){
_start:
{
if (lean_obj_tag(v_t_737_) == 0)
{
lean_object* v_k_739_; lean_object* v_v_740_; lean_object* v_l_741_; lean_object* v_r_742_; uint8_t v___x_743_; 
v_k_739_ = lean_ctor_get(v_t_737_, 1);
v_v_740_ = lean_ctor_get(v_t_737_, 2);
v_l_741_ = lean_ctor_get(v_t_737_, 3);
v_r_742_ = lean_ctor_get(v_t_737_, 4);
v___x_743_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_738_, v_k_739_);
switch(v___x_743_)
{
case 0:
{
v_t_737_ = v_l_741_;
goto _start;
}
case 1:
{
lean_object* v___x_745_; 
lean_inc(v_v_740_);
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v_v_740_);
return v___x_745_;
}
default: 
{
v_t_737_ = v_r_742_;
goto _start;
}
}
}
else
{
lean_object* v___x_747_; 
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg___boxed(lean_object* v_t_748_, lean_object* v_k_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_748_, v_k_749_);
lean_dec(v_k_749_);
lean_dec(v_t_748_);
return v_res_750_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(lean_object* v_k_751_, lean_object* v_t_752_){
_start:
{
if (lean_obj_tag(v_t_752_) == 0)
{
lean_object* v_k_753_; lean_object* v_l_754_; lean_object* v_r_755_; uint8_t v___x_756_; 
v_k_753_ = lean_ctor_get(v_t_752_, 1);
v_l_754_ = lean_ctor_get(v_t_752_, 3);
v_r_755_ = lean_ctor_get(v_t_752_, 4);
v___x_756_ = lean_nat_dec_lt(v_k_751_, v_k_753_);
if (v___x_756_ == 0)
{
uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_eq(v_k_751_, v_k_753_);
if (v___x_757_ == 0)
{
v_t_752_ = v_r_755_;
goto _start;
}
else
{
return v___x_757_;
}
}
else
{
v_t_752_ = v_l_754_;
goto _start;
}
}
else
{
uint8_t v___x_760_; 
v___x_760_ = 0;
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg___boxed(lean_object* v_k_761_, lean_object* v_t_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_761_, v_t_762_);
lean_dec(v_t_762_);
lean_dec(v_k_761_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(lean_object* v_localInst2Index_765_, lean_object* v_e_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_fvarId_769_; lean_object* v___x_770_; 
v_fvarId_769_ = l_Lean_Expr_fvarId_x21(v_e_766_);
v___x_770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_localInst2Index_765_, v_fvarId_769_);
lean_dec(v_fvarId_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_box(0);
return v___x_771_;
}
else
{
lean_object* v_val_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___y_776_; uint8_t v___x_778_; 
v_val_772_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v___x_770_, 1);
v___x_773_ = lean_st_ref_take(v___y_767_);
v___x_774_ = lean_box(0);
v___x_778_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_val_772_, v___x_773_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_val_772_, v___x_774_, v___x_773_);
v___y_776_ = v___x_779_;
goto v___jp_775_;
}
else
{
lean_dec(v_val_772_);
v___y_776_ = v___x_773_;
goto v___jp_775_;
}
v___jp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_st_ref_put(v___y_767_, v___y_776_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed(lean_object* v_localInst2Index_780_, lean_object* v_e_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(v_localInst2Index_780_, v_e_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v_e_781_);
lean_dec(v_localInst2Index_780_);
return v_res_784_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
else
{
lean_object* v_key_788_; lean_object* v_tail_789_; uint8_t v___x_790_; 
v_key_788_ = lean_ctor_get(v_x_786_, 0);
v_tail_789_ = lean_ctor_get(v_x_786_, 2);
v___x_790_ = lean_expr_eqv(v_key_788_, v_a_785_);
if (v___x_790_ == 0)
{
v_x_786_ = v_tail_789_;
goto _start;
}
else
{
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_a_792_, lean_object* v_x_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_792_, v_x_793_);
lean_dec(v_x_793_);
lean_dec_ref(v_a_792_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
return v_x_796_;
}
else
{
lean_object* v_key_798_; lean_object* v_value_799_; lean_object* v_tail_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_823_; 
v_key_798_ = lean_ctor_get(v_x_797_, 0);
v_value_799_ = lean_ctor_get(v_x_797_, 1);
v_tail_800_ = lean_ctor_get(v_x_797_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_823_ == 0)
{
v___x_802_ = v_x_797_;
v_isShared_803_ = v_isSharedCheck_823_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_tail_800_);
lean_inc(v_value_799_);
lean_inc(v_key_798_);
lean_dec(v_x_797_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_823_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v_fold_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_804_ = lean_array_get_size(v_x_796_);
v___x_805_ = l_Lean_Expr_hash(v_key_798_);
v___x_806_ = 32ULL;
v___x_807_ = lean_uint64_shift_right(v___x_805_, v___x_806_);
v_fold_808_ = lean_uint64_xor(v___x_805_, v___x_807_);
v___x_809_ = 16ULL;
v___x_810_ = lean_uint64_shift_right(v_fold_808_, v___x_809_);
v___x_811_ = lean_uint64_xor(v_fold_808_, v___x_810_);
v___x_812_ = lean_uint64_to_usize(v___x_811_);
v___x_813_ = lean_usize_of_nat(v___x_804_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_sub(v___x_813_, v___x_814_);
v___x_816_ = lean_usize_land(v___x_812_, v___x_815_);
v___x_817_ = lean_array_uget_borrowed(v_x_796_, v___x_816_);
lean_inc(v___x_817_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 2, v___x_817_);
v___x_819_ = v___x_802_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_key_798_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_value_799_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v___x_817_);
v___x_819_ = v_reuseFailAlloc_822_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; 
v___x_820_ = lean_array_uset(v_x_796_, v___x_816_, v___x_819_);
v_x_796_ = v___x_820_;
v_x_797_ = v_tail_800_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_i_824_, lean_object* v_source_825_, lean_object* v_target_826_){
_start:
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_array_get_size(v_source_825_);
v___x_828_ = lean_nat_dec_lt(v_i_824_, v___x_827_);
if (v___x_828_ == 0)
{
lean_dec_ref(v_source_825_);
lean_dec(v_i_824_);
return v_target_826_;
}
else
{
lean_object* v_es_829_; lean_object* v___x_830_; lean_object* v_source_831_; lean_object* v_target_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_es_829_ = lean_array_fget(v_source_825_, v_i_824_);
v___x_830_ = lean_box(0);
v_source_831_ = lean_array_fset(v_source_825_, v_i_824_, v___x_830_);
v_target_832_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_target_826_, v_es_829_);
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_i_824_, v___x_833_);
lean_dec(v_i_824_);
v_i_824_ = v___x_834_;
v_source_825_ = v_source_831_;
v_target_826_ = v_target_832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_data_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_nbuckets_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_837_ = lean_array_get_size(v_data_836_);
v___x_838_ = lean_unsigned_to_nat(2u);
v_nbuckets_839_ = lean_nat_mul(v___x_837_, v___x_838_);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_box(0);
v___x_842_ = lean_mk_array(v_nbuckets_839_, v___x_841_);
v___x_843_ = lean_array_propagate_mark(v_data_836_, v___x_842_);
v___x_844_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v___x_840_, v_data_836_, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(lean_object* v_m_845_, lean_object* v_a_846_, lean_object* v_b_847_){
_start:
{
lean_object* v_size_848_; lean_object* v_buckets_849_; lean_object* v___x_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v___x_853_; uint64_t v_fold_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; size_t v___x_862_; lean_object* v_bkt_863_; uint8_t v___x_864_; 
v_size_848_ = lean_ctor_get(v_m_845_, 0);
v_buckets_849_ = lean_ctor_get(v_m_845_, 1);
v___x_850_ = lean_array_get_size(v_buckets_849_);
v___x_851_ = l_Lean_Expr_hash(v_a_846_);
v___x_852_ = 32ULL;
v___x_853_ = lean_uint64_shift_right(v___x_851_, v___x_852_);
v_fold_854_ = lean_uint64_xor(v___x_851_, v___x_853_);
v___x_855_ = 16ULL;
v___x_856_ = lean_uint64_shift_right(v_fold_854_, v___x_855_);
v___x_857_ = lean_uint64_xor(v_fold_854_, v___x_856_);
v___x_858_ = lean_uint64_to_usize(v___x_857_);
v___x_859_ = lean_usize_of_nat(v___x_850_);
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_sub(v___x_859_, v___x_860_);
v___x_862_ = lean_usize_land(v___x_858_, v___x_861_);
v_bkt_863_ = lean_array_uget_borrowed(v_buckets_849_, v___x_862_);
v___x_864_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_846_, v_bkt_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_885_; 
lean_inc_ref(v_buckets_849_);
lean_inc(v_size_848_);
v_isSharedCheck_885_ = !lean_is_exclusive(v_m_845_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_886_ = lean_ctor_get(v_m_845_, 1);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_m_845_, 0);
lean_dec(v_unused_887_);
v___x_866_ = v_m_845_;
v_isShared_867_ = v_isSharedCheck_885_;
goto v_resetjp_865_;
}
else
{
lean_dec(v_m_845_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_885_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v_size_x27_869_; lean_object* v___x_870_; lean_object* v_buckets_x27_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_868_ = lean_unsigned_to_nat(1u);
v_size_x27_869_ = lean_nat_add(v_size_848_, v___x_868_);
lean_dec(v_size_848_);
lean_inc(v_bkt_863_);
v___x_870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_870_, 0, v_a_846_);
lean_ctor_set(v___x_870_, 1, v_b_847_);
lean_ctor_set(v___x_870_, 2, v_bkt_863_);
v_buckets_x27_871_ = lean_array_uset(v_buckets_849_, v___x_862_, v___x_870_);
v___x_872_ = lean_unsigned_to_nat(4u);
v___x_873_ = lean_nat_mul(v_size_x27_869_, v___x_872_);
v___x_874_ = lean_unsigned_to_nat(3u);
v___x_875_ = lean_nat_div(v___x_873_, v___x_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_array_get_size(v_buckets_x27_871_);
v___x_877_ = lean_nat_dec_le(v___x_875_, v___x_876_);
lean_dec(v___x_875_);
if (v___x_877_ == 0)
{
lean_object* v_val_878_; lean_object* v___x_880_; 
v_val_878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_buckets_x27_871_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_val_878_);
lean_ctor_set(v___x_866_, 0, v_size_x27_869_);
v___x_880_ = v___x_866_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_size_x27_869_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_val_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v___x_883_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_buckets_x27_871_);
lean_ctor_set(v___x_866_, 0, v_size_x27_869_);
v___x_883_ = v___x_866_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_size_x27_869_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_buckets_x27_871_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_dec(v_b_847_);
lean_dec_ref(v_a_846_);
return v_m_845_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_buckets_890_; lean_object* v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v_fold_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_buckets_890_ = lean_ctor_get(v_m_888_, 1);
v___x_891_ = lean_array_get_size(v_buckets_890_);
v___x_892_ = l_Lean_Expr_hash(v_a_889_);
v___x_893_ = 32ULL;
v___x_894_ = lean_uint64_shift_right(v___x_892_, v___x_893_);
v_fold_895_ = lean_uint64_xor(v___x_892_, v___x_894_);
v___x_896_ = 16ULL;
v___x_897_ = lean_uint64_shift_right(v_fold_895_, v___x_896_);
v___x_898_ = lean_uint64_xor(v_fold_895_, v___x_897_);
v___x_899_ = lean_uint64_to_usize(v___x_898_);
v___x_900_ = lean_usize_of_nat(v___x_891_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_sub(v___x_900_, v___x_901_);
v___x_903_ = lean_usize_land(v___x_899_, v___x_902_);
v___x_904_ = lean_array_uget_borrowed(v_buckets_890_, v___x_903_);
v___x_905_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_889_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_m_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_906_, v_a_907_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_m_906_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(lean_object* v_e_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_913_; lean_object* v_checked_914_; uint8_t v___x_915_; 
v___x_913_ = lean_st_ref_get(v_a_911_);
v_checked_914_ = lean_ctor_get(v___x_913_, 1);
lean_inc_ref(v_checked_914_);
lean_dec(v___x_913_);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_checked_914_, v_e_910_);
lean_dec_ref(v_checked_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v_visited_917_; lean_object* v_checked_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_928_; 
v___x_916_ = lean_st_ref_take(v_a_911_);
v_visited_917_ = lean_ctor_get(v___x_916_, 0);
v_checked_918_ = lean_ctor_get(v___x_916_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_928_ == 0)
{
v___x_920_ = v___x_916_;
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_checked_918_);
lean_inc(v_visited_917_);
lean_dec(v___x_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_922_ = lean_box(0);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_checked_918_, v_e_910_, v___x_922_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_923_);
v___x_925_ = v___x_920_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_visited_917_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v___x_923_);
v___x_925_ = v_reuseFailAlloc_927_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; 
v___x_926_ = lean_st_ref_put(v_a_911_, v___x_925_);
return v___x_915_;
}
}
}
else
{
lean_dec_ref(v_e_910_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_e_929_, lean_object* v_a_930_, lean_object* v___y_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_929_, v_a_930_);
lean_dec(v_a_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(lean_object* v_e_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; lean_object* v_visited_938_; size_t v___x_939_; size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; size_t v___x_943_; uint8_t v___x_944_; 
v___x_937_ = lean_st_ref_get(v_a_935_);
v_visited_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_visited_938_);
lean_dec(v___x_937_);
v___x_939_ = lean_ptr_addr(v_e_934_);
v___x_940_ = ((size_t)8191ULL);
v___x_941_ = lean_usize_mod(v___x_939_, v___x_940_);
v___x_942_ = lean_array_uget(v_visited_938_, v___x_941_);
lean_dec_ref(v_visited_938_);
v___x_943_ = lean_ptr_addr(v___x_942_);
lean_dec(v___x_942_);
v___x_944_ = lean_usize_dec_eq(v___x_943_, v___x_939_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v_visited_946_; lean_object* v_checked_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_956_; 
v___x_945_ = lean_st_ref_take(v_a_935_);
v_visited_946_ = lean_ctor_get(v___x_945_, 0);
v_checked_947_ = lean_ctor_get(v___x_945_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_956_ == 0)
{
v___x_949_ = v___x_945_;
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_checked_947_);
lean_inc(v_visited_946_);
lean_dec(v___x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_array_uset(v_visited_946_, v___x_941_, v_e_934_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_checked_947_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_st_ref_put(v_a_935_, v___x_953_);
return v___x_944_;
}
}
}
else
{
lean_dec_ref(v_e_934_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_e_957_, lean_object* v_a_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_957_, v_a_958_);
lean_dec(v_a_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(lean_object* v_p_962_, lean_object* v_f_963_, uint8_t v_stopWhenVisited_964_, lean_object* v_e_965_, lean_object* v_a_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___y_970_; lean_object* v_d_971_; lean_object* v_b_972_; lean_object* v___y_973_; lean_object* v___y_977_; lean_object* v___y_978_; uint8_t v___x_998_; 
lean_inc_ref(v_e_965_);
v___x_998_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_965_, v_a_966_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
lean_inc_ref(v_p_962_);
lean_inc_ref(v_e_965_);
v___x_999_ = lean_apply_1(v_p_962_, v_e_965_);
v___x_1000_ = lean_unbox(v___x_999_);
if (v___x_1000_ == 0)
{
v___y_977_ = v_a_966_;
v___y_978_ = v___y_967_;
goto v___jp_976_;
}
else
{
uint8_t v___x_1001_; 
lean_inc_ref(v_e_965_);
v___x_1001_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_965_, v_a_966_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
lean_inc_ref(v_f_963_);
lean_inc(v___y_967_);
lean_inc_ref(v_e_965_);
v___x_1002_ = lean_apply_3(v_f_963_, v_e_965_, v___y_967_, lean_box(0));
if (v_stopWhenVisited_964_ == 0)
{
v___y_977_ = v_a_966_;
v___y_978_ = v___y_967_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1003_; 
lean_dec_ref(v_e_965_);
lean_dec_ref(v_f_963_);
lean_dec_ref(v_p_962_);
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
}
else
{
v___y_977_ = v_a_966_;
v___y_978_ = v___y_967_;
goto v___jp_976_;
}
}
}
else
{
lean_object* v___x_1004_; 
lean_dec_ref(v_e_965_);
lean_dec_ref(v_f_963_);
lean_dec_ref(v_p_962_);
v___x_1004_ = lean_box(0);
return v___x_1004_;
}
v___jp_969_:
{
lean_object* v___x_974_; 
lean_inc_ref(v_f_963_);
lean_inc_ref(v_p_962_);
v___x_974_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_962_, v_f_963_, v_stopWhenVisited_964_, v_d_971_, v___y_973_, v___y_970_);
v_e_965_ = v_b_972_;
v_a_966_ = v___y_973_;
v___y_967_ = v___y_970_;
goto _start;
}
v___jp_976_:
{
switch(lean_obj_tag(v_e_965_))
{
case 7:
{
lean_object* v_binderType_979_; lean_object* v_body_980_; 
v_binderType_979_ = lean_ctor_get(v_e_965_, 1);
lean_inc_ref(v_binderType_979_);
v_body_980_ = lean_ctor_get(v_e_965_, 2);
lean_inc_ref(v_body_980_);
lean_dec_ref_known(v_e_965_, 3);
v___y_970_ = v___y_978_;
v_d_971_ = v_binderType_979_;
v_b_972_ = v_body_980_;
v___y_973_ = v___y_977_;
goto v___jp_969_;
}
case 6:
{
lean_object* v_binderType_981_; lean_object* v_body_982_; 
v_binderType_981_ = lean_ctor_get(v_e_965_, 1);
lean_inc_ref(v_binderType_981_);
v_body_982_ = lean_ctor_get(v_e_965_, 2);
lean_inc_ref(v_body_982_);
lean_dec_ref_known(v_e_965_, 3);
v___y_970_ = v___y_978_;
v_d_971_ = v_binderType_981_;
v_b_972_ = v_body_982_;
v___y_973_ = v___y_977_;
goto v___jp_969_;
}
case 8:
{
lean_object* v_type_983_; lean_object* v_value_984_; lean_object* v_body_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_type_983_ = lean_ctor_get(v_e_965_, 1);
lean_inc_ref(v_type_983_);
v_value_984_ = lean_ctor_get(v_e_965_, 2);
lean_inc_ref(v_value_984_);
v_body_985_ = lean_ctor_get(v_e_965_, 3);
lean_inc_ref(v_body_985_);
lean_dec_ref_known(v_e_965_, 4);
lean_inc_ref_n(v_f_963_, 2);
lean_inc_ref_n(v_p_962_, 2);
v___x_986_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_962_, v_f_963_, v_stopWhenVisited_964_, v_type_983_, v___y_977_, v___y_978_);
v___x_987_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_962_, v_f_963_, v_stopWhenVisited_964_, v_value_984_, v___y_977_, v___y_978_);
v_e_965_ = v_body_985_;
v_a_966_ = v___y_977_;
v___y_967_ = v___y_978_;
goto _start;
}
case 5:
{
lean_object* v_fn_989_; lean_object* v_arg_990_; lean_object* v___x_991_; 
v_fn_989_ = lean_ctor_get(v_e_965_, 0);
lean_inc_ref(v_fn_989_);
v_arg_990_ = lean_ctor_get(v_e_965_, 1);
lean_inc_ref(v_arg_990_);
lean_dec_ref_known(v_e_965_, 2);
lean_inc_ref(v_f_963_);
lean_inc_ref(v_p_962_);
v___x_991_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_962_, v_f_963_, v_stopWhenVisited_964_, v_fn_989_, v___y_977_, v___y_978_);
v_e_965_ = v_arg_990_;
v_a_966_ = v___y_977_;
v___y_967_ = v___y_978_;
goto _start;
}
case 10:
{
lean_object* v_expr_993_; 
v_expr_993_ = lean_ctor_get(v_e_965_, 1);
lean_inc_ref(v_expr_993_);
lean_dec_ref_known(v_e_965_, 2);
v_e_965_ = v_expr_993_;
v_a_966_ = v___y_977_;
v___y_967_ = v___y_978_;
goto _start;
}
case 11:
{
lean_object* v_struct_995_; 
v_struct_995_ = lean_ctor_get(v_e_965_, 2);
lean_inc_ref(v_struct_995_);
lean_dec_ref_known(v_e_965_, 3);
v_e_965_ = v_struct_995_;
v_a_966_ = v___y_977_;
v___y_967_ = v___y_978_;
goto _start;
}
default: 
{
lean_object* v___x_997_; 
lean_dec_ref(v_e_965_);
lean_dec_ref(v_f_963_);
lean_dec_ref(v_p_962_);
v___x_997_ = lean_box(0);
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg___boxed(lean_object* v_p_1005_, lean_object* v_f_1006_, lean_object* v_stopWhenVisited_1007_, lean_object* v_e_1008_, lean_object* v_a_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1012_; lean_object* v_res_1013_; 
v_stopWhenVisited_boxed_1012_ = lean_unbox(v_stopWhenVisited_1007_);
v_res_1013_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1005_, v_f_1006_, v_stopWhenVisited_boxed_1012_, v_e_1008_, v_a_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec(v_a_1009_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(lean_object* v_p_1014_, lean_object* v_f_1015_, lean_object* v_e_1016_, uint8_t v_stopWhenVisited_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1020_ = l_Lean_ForEachExprWhere_initCache;
v___x_1021_ = lean_st_mk_ref(v___x_1020_);
v___x_1022_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1014_, v_f_1015_, v_stopWhenVisited_1017_, v_e_1016_, v___x_1021_, v___y_1018_);
v___x_1023_ = lean_st_ref_get(v___x_1021_);
lean_dec(v___x_1021_);
lean_dec(v___x_1023_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg___boxed(lean_object* v_p_1024_, lean_object* v_f_1025_, lean_object* v_e_1026_, lean_object* v_stopWhenVisited_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1030_; lean_object* v_res_1031_; 
v_stopWhenVisited_boxed_1030_ = lean_unbox(v_stopWhenVisited_1027_);
v_res_1031_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1024_, v_f_1025_, v_e_1026_, v_stopWhenVisited_boxed_1030_, v___y_1028_);
lean_dec(v___y_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(lean_object* v_usedInstIdxs_1033_, lean_object* v___f_1034_, lean_object* v_e_1035_, uint8_t v___x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1039_ = lean_st_mk_ref(v_usedInstIdxs_1033_);
v___x_1040_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0));
v___x_1041_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v___x_1040_, v___f_1034_, v_e_1035_, v___x_1036_, v___x_1039_);
v___x_1042_ = lean_st_ref_get(v___x_1039_);
lean_dec(v___x_1039_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed(lean_object* v_usedInstIdxs_1044_, lean_object* v___f_1045_, lean_object* v_e_1046_, lean_object* v___x_1047_, lean_object* v_x_1048_, lean_object* v___y_1049_){
_start:
{
uint8_t v___x_6833__boxed_1050_; lean_object* v_res_1051_; 
v___x_6833__boxed_1050_ = lean_unbox(v___x_1047_);
v_res_1051_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(v_usedInstIdxs_1044_, v___f_1045_, v_e_1046_, v___x_6833__boxed_1050_, v_x_1048_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(lean_object* v_usedInstIdxs_1052_, lean_object* v_localInst2Index_1053_, lean_object* v_e_1054_){
_start:
{
if (lean_obj_tag(v_localInst2Index_1053_) == 0)
{
lean_object* v___f_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v_snd_1060_; 
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1055_, 0, v_localInst2Index_1053_);
v___x_1056_ = 0;
v___x_1057_ = lean_box(v___x_1056_);
v___f_1058_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1058_, 0, v_usedInstIdxs_1052_);
lean_closure_set(v___f_1058_, 1, v___f_1055_);
lean_closure_set(v___f_1058_, 2, v_e_1054_);
lean_closure_set(v___f_1058_, 3, v___x_1057_);
v___x_1059_ = l_runST___redArg(v___f_1058_);
v_snd_1060_ = lean_ctor_get(v___x_1059_, 1);
lean_inc(v_snd_1060_);
lean_dec(v___x_1059_);
return v_snd_1060_;
}
else
{
lean_dec_ref(v_e_1054_);
return v_usedInstIdxs_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(lean_object* v_00_u03b4_1061_, lean_object* v_t_1062_, lean_object* v_k_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_1062_, v_k_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___boxed(lean_object* v_00_u03b4_1065_, lean_object* v_t_1066_, lean_object* v_k_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(v_00_u03b4_1065_, v_t_1066_, v_k_1067_);
lean_dec(v_k_1067_);
lean_dec(v_t_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(lean_object* v_00_u03b2_1069_, lean_object* v_k_1070_, lean_object* v_t_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_1070_, v_t_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___boxed(lean_object* v_00_u03b2_1073_, lean_object* v_k_1074_, lean_object* v_t_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(v_00_u03b2_1073_, v_k_1074_, v_t_1075_);
lean_dec(v_t_1075_);
lean_dec(v_k_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2(lean_object* v_00_u03b2_1078_, lean_object* v_k_1079_, lean_object* v_v_1080_, lean_object* v_t_1081_, lean_object* v_hl_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_1079_, v_v_1080_, v_t_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(lean_object* v_x_1084_, lean_object* v_p_1085_, lean_object* v_f_1086_, lean_object* v_e_1087_, uint8_t v_stopWhenVisited_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1085_, v_f_1086_, v_e_1087_, v_stopWhenVisited_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___boxed(lean_object* v_x_1092_, lean_object* v_p_1093_, lean_object* v_f_1094_, lean_object* v_e_1095_, lean_object* v_stopWhenVisited_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1099_; lean_object* v_res_1100_; 
v_stopWhenVisited_boxed_1099_ = lean_unbox(v_stopWhenVisited_1096_);
v_res_1100_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(v_x_1092_, v_p_1093_, v_f_1094_, v_e_1095_, v_stopWhenVisited_boxed_1099_, v___y_1097_);
lean_dec(v___y_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(lean_object* v_x_1101_, lean_object* v_e_1102_, lean_object* v_a_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_1102_, v_a_1103_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___boxed(lean_object* v_x_1107_, lean_object* v_e_1108_, lean_object* v_a_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_res_1112_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(v_x_1107_, v_e_1108_, v_a_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec(v_a_1109_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(lean_object* v_x_1114_, lean_object* v_p_1115_, lean_object* v_f_1116_, uint8_t v_stopWhenVisited_1117_, lean_object* v_e_1118_, lean_object* v_a_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1115_, v_f_1116_, v_stopWhenVisited_1117_, v_e_1118_, v_a_1119_, v___y_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___boxed(lean_object* v_x_1123_, lean_object* v_p_1124_, lean_object* v_f_1125_, lean_object* v_stopWhenVisited_1126_, lean_object* v_e_1127_, lean_object* v_a_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1131_; lean_object* v_res_1132_; 
v_stopWhenVisited_boxed_1131_ = lean_unbox(v_stopWhenVisited_1126_);
v_res_1132_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(v_x_1123_, v_p_1124_, v_f_1125_, v_stopWhenVisited_boxed_1131_, v_e_1127_, v_a_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec(v_a_1128_);
return v_res_1132_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(lean_object* v_x_1133_, lean_object* v_e_1134_, lean_object* v_a_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_1134_, v_a_1135_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___boxed(lean_object* v_x_1139_, lean_object* v_e_1140_, lean_object* v_a_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(v_x_1139_, v_e_1140_, v_a_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec(v_a_1141_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1146_, lean_object* v_m_1147_, lean_object* v_a_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_1147_, v_a_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1150_, lean_object* v_m_1151_, lean_object* v_a_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(v_00_u03b2_1150_, v_m_1151_, v_a_1152_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_m_1151_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1155_, lean_object* v_m_1156_, lean_object* v_a_1157_, lean_object* v_b_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_m_1156_, v_a_1157_, v_b_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1160_, lean_object* v_a_1161_, lean_object* v_x_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_1161_, v_x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1164_, lean_object* v_a_1165_, lean_object* v_x_1166_){
_start:
{
uint8_t v_res_1167_; lean_object* v_r_1168_; 
v_res_1167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(v_00_u03b2_1164_, v_a_1165_, v_x_1166_);
lean_dec(v_x_1166_);
lean_dec_ref(v_a_1165_);
v_r_1168_ = lean_box(v_res_1167_);
return v_r_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_1169_, lean_object* v_data_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_data_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1172_, lean_object* v_i_1173_, lean_object* v_source_1174_, lean_object* v_target_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_i_1173_, v_source_1174_, v_target_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11(lean_object* v_00_u03b2_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_x_1178_, v_x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10(void){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Array_mkArray0___redArg();
return v___x_1197_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0));
v___x_1213_ = l_String_toRawSubstring_x27(v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(lean_object* v_upperBound_1226_, lean_object* v_usedInstIdxs_1227_, lean_object* v_a_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_a_1234_; uint8_t v___x_1238_; 
v___x_1238_ = lean_nat_dec_lt(v_a_1228_, v_upperBound_1226_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec(v_a_1228_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_b_1229_);
return v___x_1239_;
}
else
{
lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1296_; 
v_fst_1240_ = lean_ctor_get(v_b_1229_, 0);
v_snd_1241_ = lean_ctor_get(v_b_1229_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_b_1229_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1243_ = v_b_1229_;
v_isShared_1244_ = v_isSharedCheck_1296_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
lean_dec(v_b_1229_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1296_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1));
v___x_1246_ = l_Lean_Core_mkFreshUserName(v___x_1245_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v_toCold_1248_; lean_object* v_ref_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v_toCold_1248_ = lean_ctor_get(v___y_1230_, 0);
v_ref_1249_ = lean_ctor_get(v___y_1230_, 2);
v___x_1250_ = l_Lean_mkIdent(v_a_1247_);
lean_inc(v___x_1250_);
v___x_1251_ = lean_array_push(v_fst_1240_, v___x_1250_);
v___x_1252_ = 0;
v___x_1253_ = l_Lean_SourceInfo_fromRef(v_ref_1249_, v___x_1252_);
v___x_1254_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6));
v___x_1255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_1253_, 5);
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1253_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1258_ = l_Lean_Syntax_node1(v___x_1253_, v___x_1257_, v___x_1250_);
v___x_1259_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1253_);
lean_ctor_set(v___x_1260_, 1, v___x_1257_);
lean_ctor_set(v___x_1260_, 2, v___x_1259_);
v___x_1261_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_1262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1253_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_inc_ref(v___x_1260_);
lean_inc(v___x_1258_);
v___x_1263_ = l_Lean_Syntax_node4(v___x_1253_, v___x_1254_, v___x_1256_, v___x_1258_, v___x_1260_, v___x_1262_);
v___x_1264_ = lean_array_push(v_snd_1241_, v___x_1263_);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_a_1228_, v_usedInstIdxs_1227_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1260_, 3);
lean_dec(v___x_1258_);
lean_dec(v___x_1253_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1264_);
lean_ctor_set(v___x_1243_, 0, v___x_1251_);
v___x_1267_ = v___x_1243_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1264_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v_a_1234_ = v___x_1267_;
goto v___jp_1233_;
}
}
else
{
lean_object* v_quotContext_1269_; lean_object* v_currMacroScope_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v_quotContext_1269_ = lean_ctor_get(v_toCold_1248_, 8);
v_currMacroScope_1270_ = lean_ctor_get(v_toCold_1248_, 9);
v___x_1271_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13));
v___x_1272_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14));
lean_inc_n(v___x_1253_, 4);
v___x_1273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1253_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1275_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1276_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1270_);
lean_inc(v_quotContext_1269_);
v___x_1277_ = l_Lean_addMacroScope(v_quotContext_1269_, v___x_1276_, v_currMacroScope_1270_);
v___x_1278_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1279_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1253_);
lean_ctor_set(v___x_1279_, 1, v___x_1275_);
lean_ctor_set(v___x_1279_, 2, v___x_1277_);
lean_ctor_set(v___x_1279_, 3, v___x_1278_);
v___x_1280_ = l_Lean_Syntax_node2(v___x_1253_, v___x_1274_, v___x_1279_, v___x_1258_);
v___x_1281_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22));
v___x_1282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1253_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_Syntax_node4(v___x_1253_, v___x_1271_, v___x_1273_, v___x_1260_, v___x_1280_, v___x_1282_);
v___x_1284_ = lean_array_push(v___x_1264_, v___x_1283_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1284_);
lean_ctor_set(v___x_1243_, 0, v___x_1251_);
v___x_1286_ = v___x_1243_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
v_a_1234_ = v___x_1286_;
goto v___jp_1233_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_dec(v_a_1228_);
v_a_1288_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1246_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1246_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
v___jp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v_a_1228_, v___x_1235_);
lean_dec(v_a_1228_);
v_a_1228_ = v___x_1236_;
v_b_1229_ = v_a_1234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___boxed(lean_object* v_upperBound_1297_, lean_object* v_usedInstIdxs_1298_, lean_object* v_a_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1297_, v_usedInstIdxs_1298_, v_a_1299_, v_b_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v_usedInstIdxs_1298_);
lean_dec(v_upperBound_1297_);
return v_res_1304_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_box(1);
v___x_1306_ = l_Lean_MessageData_ofFormat(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2));
v___x_1311_ = l_Lean_MessageData_ofFormat(v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
if (lean_obj_tag(v_x_1313_) == 0)
{
return v_x_1312_;
}
else
{
lean_object* v_head_1314_; lean_object* v_tail_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1337_; 
v_head_1314_ = lean_ctor_get(v_x_1313_, 0);
v_tail_1315_ = lean_ctor_get(v_x_1313_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1313_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1317_ = v_x_1313_;
v_isShared_1318_ = v_isSharedCheck_1337_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_tail_1315_);
lean_inc(v_head_1314_);
lean_dec(v_x_1313_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1337_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_before_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1335_; 
v_before_1319_ = lean_ctor_get(v_head_1314_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_head_1314_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_head_1314_, 1);
lean_dec(v_unused_1336_);
v___x_1321_ = v_head_1314_;
v_isShared_1322_ = v_isSharedCheck_1335_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_before_1319_);
lean_dec(v_head_1314_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1335_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 7);
lean_ctor_set(v___x_1321_, 1, v___x_1323_);
lean_ctor_set(v___x_1321_, 0, v_x_1312_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_x_1312_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 7);
lean_ctor_set(v___x_1317_, 1, v___x_1326_);
lean_ctor_set(v___x_1317_, 0, v___x_1325_);
v___x_1328_ = v___x_1317_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_MessageData_ofSyntax(v_before_1319_);
v___x_1330_ = l_Lean_indentD(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1328_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v_x_1312_ = v___x_1331_;
v_x_1313_ = v_tail_1315_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_1338_, lean_object* v_opt_1339_){
_start:
{
lean_object* v_name_1340_; lean_object* v_defValue_1341_; lean_object* v_map_1342_; lean_object* v___x_1343_; 
v_name_1340_ = lean_ctor_get(v_opt_1339_, 0);
v_defValue_1341_ = lean_ctor_get(v_opt_1339_, 1);
v_map_1342_ = lean_ctor_get(v_opts_1338_, 0);
v___x_1343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1342_, v_name_1340_);
if (lean_obj_tag(v___x_1343_) == 0)
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_unbox(v_defValue_1341_);
return v___x_1344_;
}
else
{
lean_object* v_val_1345_; 
v_val_1345_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v___x_1343_, 1);
if (lean_obj_tag(v_val_1345_) == 1)
{
uint8_t v_v_1346_; 
v_v_1346_ = lean_ctor_get_uint8(v_val_1345_, 0);
lean_dec_ref_known(v_val_1345_, 0);
return v_v_1346_;
}
else
{
uint8_t v___x_1347_; 
lean_dec(v_val_1345_);
v___x_1347_ = lean_unbox(v_defValue_1341_);
return v___x_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_1348_, lean_object* v_opt_1349_){
_start:
{
uint8_t v_res_1350_; lean_object* v_r_1351_; 
v_res_1350_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_1348_, v_opt_1349_);
lean_dec_ref(v_opt_1349_);
lean_dec_ref(v_opts_1348_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1356_ = l_Lean_MessageData_ofFormat(v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_1357_, lean_object* v_macroStack_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1359_);
v___x_1362_ = l_Lean_Elab_pp_macroStack;
v___x_1363_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v___x_1361_, v___x_1362_);
lean_dec_ref(v___x_1361_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_dec(v_macroStack_1358_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_msgData_1357_);
return v___x_1364_;
}
else
{
if (lean_obj_tag(v_macroStack_1358_) == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_msgData_1357_);
return v___x_1365_;
}
else
{
lean_object* v_head_1366_; lean_object* v_after_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1382_; 
v_head_1366_ = lean_ctor_get(v_macroStack_1358_, 0);
lean_inc(v_head_1366_);
v_after_1367_ = lean_ctor_get(v_head_1366_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_head_1366_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_head_1366_, 0);
lean_dec(v_unused_1383_);
v___x_1369_ = v_head_1366_;
v_isShared_1370_ = v_isSharedCheck_1382_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_after_1367_);
lean_dec(v_head_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1382_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 7);
lean_ctor_set(v___x_1369_, 1, v___x_1371_);
lean_ctor_set(v___x_1369_, 0, v_msgData_1357_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_msgData_1357_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_msgData_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1374_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_MessageData_ofSyntax(v_after_1367_);
v___x_1377_ = l_Lean_indentD(v___x_1376_);
v_msgData_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1378_, 0, v___x_1375_);
lean_ctor_set(v_msgData_1378_, 1, v___x_1377_);
v___x_1379_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_1378_, v_macroStack_1358_);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1384_, lean_object* v_macroStack_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1384_, v_macroStack_1385_, v___y_1386_);
lean_dec_ref(v___y_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_ref_1397_; lean_object* v_macroStack_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1411_; 
v_ref_1397_ = lean_ctor_get(v___y_1394_, 2);
v_macroStack_1398_ = lean_ctor_get(v___y_1390_, 1);
v___x_1399_ = l_Lean_Elab_getBetterRef(v_ref_1397_, v_macroStack_1398_);
v___x_1400_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1389_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
lean_inc(v_macroStack_1398_);
v___x_1402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_a_1401_, v_macroStack_1398_, v___y_1394_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1399_);
lean_ctor_set(v___x_1407_, 1, v_a_1403_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 1);
lean_ctor_set(v___x_1405_, 0, v___x_1407_);
v___x_1409_ = v___x_1405_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1420_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0));
v___x_1423_ = l_Lean_stringToMessageData(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2));
v___x_1426_ = l_Lean_stringToMessageData(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(lean_object* v_constName_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v_env_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_st_ref_get(v___y_1433_);
v_env_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc_ref(v_env_1436_);
lean_dec(v___x_1435_);
lean_inc(v_constName_1427_);
v___x_1437_ = l_Lean_isInductiveCore_x3f(v_env_1436_, v_constName_1427_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1438_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_1439_ = 0;
v___x_1440_ = l_Lean_MessageData_ofConstName(v_constName_1427_, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1438_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_1443_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1444_;
}
else
{
lean_object* v_val_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_constName_1427_);
v_val_1445_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1437_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_val_1445_);
lean_dec(v___x_1437_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 0);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_val_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___boxed(lean_object* v_constName_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_constName_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(size_t v_sz_1462_, size_t v_i_1463_, lean_object* v_bs_1464_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_usize_dec_lt(v_i_1463_, v_sz_1462_);
if (v___x_1465_ == 0)
{
return v_bs_1464_;
}
else
{
lean_object* v_v_1466_; lean_object* v___x_1467_; lean_object* v_bs_x27_1468_; size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v_v_1466_ = lean_array_uget(v_bs_1464_, v_i_1463_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v_bs_x27_1468_ = lean_array_uset(v_bs_1464_, v_i_1463_, v___x_1467_);
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_add(v_i_1463_, v___x_1469_);
v___x_1471_ = lean_array_uset(v_bs_x27_1468_, v_i_1463_, v_v_1466_);
v_i_1463_ = v___x_1470_;
v_bs_1464_ = v___x_1471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0___boxed(lean_object* v_sz_1473_, lean_object* v_i_1474_, lean_object* v_bs_1475_){
_start:
{
size_t v_sz_boxed_1476_; size_t v_i_boxed_1477_; lean_object* v_res_1478_; 
v_sz_boxed_1476_ = lean_unbox_usize(v_sz_1473_);
lean_dec(v_sz_1473_);
v_i_boxed_1477_ = lean_unbox_usize(v_i_1474_);
lean_dec(v_i_1474_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_boxed_1476_, v_i_boxed_1477_, v_bs_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(lean_object* v_inductiveTypeName_1556_, lean_object* v_instId_1557_, lean_object* v_usedInstIdxs_1558_, lean_object* v_auxFunId_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v___x_1567_; 
lean_inc(v_inductiveTypeName_1556_);
v___x_1567_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_1556_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_numParams_1569_; lean_object* v_numIndices_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v_numParams_1569_ = lean_ctor_get(v_a_1568_, 1);
lean_inc(v_numParams_1569_);
v_numIndices_1570_ = lean_ctor_get(v_a_1568_, 2);
lean_inc(v_numIndices_1570_);
lean_dec(v_a_1568_);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = lean_nat_add(v_numParams_1569_, v_numIndices_1570_);
lean_dec(v_numIndices_1570_);
lean_dec(v_numParams_1569_);
v___x_1573_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1));
v___x_1574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v___x_1572_, v_usedInstIdxs_1558_, v___x_1571_, v___x_1573_, v_a_1564_, v_a_1565_);
lean_dec(v___x_1572_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1652_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1652_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1652_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_fst_1579_; lean_object* v_snd_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1651_; 
v_fst_1579_ = lean_ctor_get(v_a_1575_, 0);
v_snd_1580_ = lean_ctor_get(v_a_1575_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_a_1575_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1582_ = v_a_1575_;
v_isShared_1583_ = v_isSharedCheck_1651_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_snd_1580_);
lean_inc(v_fst_1579_);
lean_dec(v_a_1575_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1651_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_toCold_1584_; lean_object* v_ref_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v_toCold_1584_ = lean_ctor_get(v_a_1564_, 0);
v_ref_1585_ = lean_ctor_get(v_a_1564_, 2);
v___x_1586_ = 0;
v___x_1587_ = l_Lean_SourceInfo_fromRef(v_ref_1585_, v___x_1586_);
v___x_1588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1589_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3));
v___x_1590_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4));
lean_inc(v___x_1587_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 2);
lean_ctor_set(v___x_1582_, 1, v___x_1590_);
lean_ctor_set(v___x_1582_, 0, v___x_1587_);
v___x_1592_ = v___x_1582_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v_quotContext_1595_; lean_object* v_currMacroScope_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; size_t v_sz_1615_; size_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1593_ = l_Lean_mkCIdent(v_inductiveTypeName_1556_);
lean_inc_n(v___x_1587_, 24);
v___x_1594_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1589_, v___x_1592_, v___x_1593_);
v_quotContext_1595_ = lean_ctor_get(v_toCold_1584_, 8);
v_currMacroScope_1596_ = lean_ctor_get(v_toCold_1584_, 9);
v___x_1597_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1598_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1599_ = l_Array_append___redArg(v___x_1598_, v_fst_1579_);
lean_dec(v_fst_1579_);
v___x_1600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1587_);
lean_ctor_set(v___x_1600_, 1, v___x_1597_);
lean_ctor_set(v___x_1600_, 2, v___x_1599_);
v___x_1601_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1588_, v___x_1594_, v___x_1600_);
v___x_1602_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7));
v___x_1603_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9));
v___x_1604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1587_);
lean_ctor_set(v___x_1604_, 1, v___x_1597_);
lean_ctor_set(v___x_1604_, 2, v___x_1598_);
lean_inc_ref_n(v___x_1604_, 12);
v___x_1605_ = l_Lean_Syntax_node7(v___x_1587_, v___x_1603_, v___x_1604_, v___x_1604_, v___x_1604_, v___x_1604_, v___x_1604_, v___x_1604_, v___x_1604_);
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10));
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11));
v___x_1608_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13));
v___x_1609_ = l_Lean_Syntax_node1(v___x_1587_, v___x_1608_, v___x_1604_);
v___x_1610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1587_);
lean_ctor_set(v___x_1610_, 1, v___x_1606_);
v___x_1611_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15));
v___x_1612_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1611_, v_instId_1557_, v___x_1604_);
v___x_1613_ = l_Lean_Syntax_node1(v___x_1587_, v___x_1597_, v___x_1612_);
v___x_1614_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17));
v_sz_1615_ = lean_array_size(v_snd_1580_);
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_1615_, v___x_1616_, v_snd_1580_);
v___x_1618_ = l_Array_append___redArg(v___x_1598_, v___x_1617_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1587_);
lean_ctor_set(v___x_1619_, 1, v___x_1597_);
lean_ctor_set(v___x_1619_, 2, v___x_1618_);
v___x_1620_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19));
v___x_1621_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20));
v___x_1622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1587_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1624_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1596_);
lean_inc(v_quotContext_1595_);
v___x_1625_ = l_Lean_addMacroScope(v_quotContext_1595_, v___x_1624_, v_currMacroScope_1596_);
v___x_1626_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1627_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1587_);
lean_ctor_set(v___x_1627_, 1, v___x_1623_);
lean_ctor_set(v___x_1627_, 2, v___x_1625_);
lean_ctor_set(v___x_1627_, 3, v___x_1626_);
v___x_1628_ = l_Lean_Syntax_node1(v___x_1587_, v___x_1597_, v___x_1601_);
v___x_1629_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1588_, v___x_1627_, v___x_1628_);
v___x_1630_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1620_, v___x_1622_, v___x_1629_);
v___x_1631_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1614_, v___x_1619_, v___x_1630_);
v___x_1632_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22));
v___x_1633_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1587_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25));
v___x_1636_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26));
v___x_1637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1587_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = l_Lean_Syntax_node1(v___x_1587_, v___x_1597_, v_auxFunId_1559_);
v___x_1639_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27));
v___x_1640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1587_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_Syntax_node3(v___x_1587_, v___x_1635_, v___x_1637_, v___x_1638_, v___x_1640_);
v___x_1642_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30));
v___x_1643_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1642_, v___x_1604_, v___x_1604_);
v___x_1644_ = l_Lean_Syntax_node4(v___x_1587_, v___x_1632_, v___x_1634_, v___x_1641_, v___x_1643_, v___x_1604_);
v___x_1645_ = l_Lean_Syntax_node6(v___x_1587_, v___x_1607_, v___x_1609_, v___x_1610_, v___x_1604_, v___x_1613_, v___x_1631_, v___x_1644_);
v___x_1646_ = l_Lean_Syntax_node2(v___x_1587_, v___x_1602_, v___x_1605_, v___x_1645_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1646_);
v___x_1648_ = v___x_1577_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
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
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_auxFunId_1559_);
lean_dec(v_instId_1557_);
lean_dec(v_inductiveTypeName_1556_);
v_a_1653_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1574_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1574_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_auxFunId_1559_);
lean_dec(v_instId_1557_);
lean_dec(v_inductiveTypeName_1556_);
v_a_1661_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1567_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1567_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___boxed(lean_object* v_inductiveTypeName_1669_, lean_object* v_instId_1670_, lean_object* v_usedInstIdxs_1671_, lean_object* v_auxFunId_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_1669_, v_instId_1670_, v_usedInstIdxs_1671_, v_auxFunId_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_usedInstIdxs_1671_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(lean_object* v_upperBound_1681_, lean_object* v_usedInstIdxs_1682_, lean_object* v_inst_1683_, lean_object* v_R_1684_, lean_object* v_a_1685_, lean_object* v_b_1686_, lean_object* v_c_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1681_, v_usedInstIdxs_1682_, v_a_1685_, v_b_1686_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___boxed(lean_object* v_upperBound_1696_, lean_object* v_usedInstIdxs_1697_, lean_object* v_inst_1698_, lean_object* v_R_1699_, lean_object* v_a_1700_, lean_object* v_b_1701_, lean_object* v_c_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(v_upperBound_1696_, v_usedInstIdxs_1697_, v_inst_1698_, v_R_1699_, v_a_1700_, v_b_1701_, v_c_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v_usedInstIdxs_1697_);
lean_dec(v_upperBound_1696_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_object* v_00_u03b1_1711_, lean_object* v_msg_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1721_, lean_object* v_msg_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(v_00_u03b1_1721_, v_msg_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(lean_object* v_msgData_1731_, lean_object* v_macroStack_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1731_, v_macroStack_1732_, v___y_1737_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1741_, lean_object* v_macroStack_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(v_msgData_1741_, v_macroStack_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1750_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_unsigned_to_nat(32u);
v___x_1752_ = lean_mk_empty_array_with_capacity(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1754_ = ((size_t)5ULL);
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = lean_unsigned_to_nat(32u);
v___x_1757_ = lean_mk_empty_array_with_capacity(v___x_1756_);
v___x_1758_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0);
v___x_1759_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1757_);
lean_ctor_set(v___x_1759_, 2, v___x_1755_);
lean_ctor_set(v___x_1759_, 3, v___x_1755_);
lean_ctor_set_usize(v___x_1759_, 4, v___x_1754_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; lean_object* v_traceState_1763_; lean_object* v_traces_1764_; lean_object* v___x_1765_; lean_object* v_traceState_1766_; lean_object* v_env_1767_; lean_object* v_nextMacroScope_1768_; lean_object* v_ngen_1769_; lean_object* v_auxDeclNGen_1770_; lean_object* v_cache_1771_; lean_object* v_recordedDeps_1772_; lean_object* v_messages_1773_; lean_object* v_infoState_1774_; lean_object* v_snapshotTasks_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1794_; 
v___x_1762_ = lean_st_ref_get(v___y_1760_);
v_traceState_1763_ = lean_ctor_get(v___x_1762_, 4);
lean_inc_ref(v_traceState_1763_);
lean_dec(v___x_1762_);
v_traces_1764_ = lean_ctor_get(v_traceState_1763_, 0);
lean_inc_ref(v_traces_1764_);
lean_dec_ref(v_traceState_1763_);
v___x_1765_ = lean_st_ref_take(v___y_1760_);
v_traceState_1766_ = lean_ctor_get(v___x_1765_, 4);
v_env_1767_ = lean_ctor_get(v___x_1765_, 0);
v_nextMacroScope_1768_ = lean_ctor_get(v___x_1765_, 1);
v_ngen_1769_ = lean_ctor_get(v___x_1765_, 2);
v_auxDeclNGen_1770_ = lean_ctor_get(v___x_1765_, 3);
v_cache_1771_ = lean_ctor_get(v___x_1765_, 5);
v_recordedDeps_1772_ = lean_ctor_get(v___x_1765_, 6);
v_messages_1773_ = lean_ctor_get(v___x_1765_, 7);
v_infoState_1774_ = lean_ctor_get(v___x_1765_, 8);
v_snapshotTasks_1775_ = lean_ctor_get(v___x_1765_, 9);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1777_ = v___x_1765_;
v_isShared_1778_ = v_isSharedCheck_1794_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_snapshotTasks_1775_);
lean_inc(v_infoState_1774_);
lean_inc(v_messages_1773_);
lean_inc(v_recordedDeps_1772_);
lean_inc(v_cache_1771_);
lean_inc(v_traceState_1766_);
lean_inc(v_auxDeclNGen_1770_);
lean_inc(v_ngen_1769_);
lean_inc(v_nextMacroScope_1768_);
lean_inc(v_env_1767_);
lean_dec(v___x_1765_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1794_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
uint64_t v_tid_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1792_; 
v_tid_1779_ = lean_ctor_get_uint64(v_traceState_1766_, sizeof(void*)*1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_traceState_1766_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_traceState_1766_, 0);
lean_dec(v_unused_1793_);
v___x_1781_ = v_traceState_1766_;
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v_traceState_1766_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1783_);
v___x_1785_ = v___x_1781_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1783_);
lean_ctor_set_uint64(v_reuseFailAlloc_1791_, sizeof(void*)*1, v_tid_1779_);
v___x_1785_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 4, v___x_1785_);
v___x_1787_ = v___x_1777_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_env_1767_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_nextMacroScope_1768_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_ngen_1769_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_auxDeclNGen_1770_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1790_, 5, v_cache_1771_);
lean_ctor_set(v_reuseFailAlloc_1790_, 6, v_recordedDeps_1772_);
lean_ctor_set(v_reuseFailAlloc_1790_, 7, v_messages_1773_);
lean_ctor_set(v_reuseFailAlloc_1790_, 8, v_infoState_1774_);
lean_ctor_set(v_reuseFailAlloc_1790_, 9, v_snapshotTasks_1775_);
v___x_1787_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_st_ref_put(v___y_1760_, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_traces_1764_);
return v___x_1789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___boxed(lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1795_);
lean_dec(v___y_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object* v_x_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
v___x_1822_ = lean_apply_7(v_x_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, lean_box(0));
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object* v_x_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(v_x_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object* v_mvarId_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___f_1841_; lean_object* v___x_1842_; 
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1841_, 0, v_x_1833_);
lean_closure_set(v___f_1841_, 1, v___y_1834_);
lean_closure_set(v___f_1841_, 2, v___y_1835_);
v___x_1842_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1832_, v___f_1841_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
return v___x_1842_;
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object* v_mvarId_1851_, lean_object* v_x_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1851_, v_x_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object* v_00_u03b1_1861_, lean_object* v_mvarId_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1862_, v_x_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object* v_00_u03b1_1872_, lean_object* v_mvarId_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(v_00_u03b1_1872_, v_mvarId_1873_, v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1882_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0));
v___x_1885_ = l_Lean_stringToMessageData(v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object* v_a_1886_, lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1895_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1);
v___x_1896_ = lean_unsigned_to_nat(30u);
v___x_1897_ = l_Lean_inlineExprTrailing(v_a_1886_, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1895_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object* v_a_1900_, lean_object* v_x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(v_a_1900_, v_x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec_ref(v_x_1901_);
return v_res_1909_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(lean_object* v_e_1910_){
_start:
{
if (lean_obj_tag(v_e_1910_) == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = 2;
return v___x_1911_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = 0;
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___boxed(lean_object* v_e_1913_){
_start:
{
uint8_t v_res_1914_; lean_object* v_r_1915_; 
v_res_1914_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_e_1913_);
lean_dec_ref(v_e_1913_);
v_r_1915_ = lean_box(v_res_1914_);
return v_r_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object* v_opts_1916_, lean_object* v_opt_1917_){
_start:
{
lean_object* v_name_1918_; lean_object* v_defValue_1919_; lean_object* v_map_1920_; lean_object* v___x_1921_; 
v_name_1918_ = lean_ctor_get(v_opt_1917_, 0);
v_defValue_1919_ = lean_ctor_get(v_opt_1917_, 1);
v_map_1920_ = lean_ctor_get(v_opts_1916_, 0);
v___x_1921_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1920_, v_name_1918_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_inc(v_defValue_1919_);
return v_defValue_1919_;
}
else
{
lean_object* v_val_1922_; 
v_val_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_val_1922_);
lean_dec_ref_known(v___x_1921_, 1);
if (lean_obj_tag(v_val_1922_) == 3)
{
lean_object* v_v_1923_; 
v_v_1923_ = lean_ctor_get(v_val_1922_, 0);
lean_inc(v_v_1923_);
lean_dec_ref_known(v_val_1922_, 1);
return v_v_1923_;
}
else
{
lean_dec(v_val_1922_);
lean_inc(v_defValue_1919_);
return v_defValue_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___boxed(lean_object* v_opts_1924_, lean_object* v_opt_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_1924_, v_opt_1925_);
lean_dec_ref(v_opt_1925_);
lean_dec_ref(v_opts_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_a_1929_ = lean_ctor_get(v_x_1927_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v_x_1927_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v_x_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v_x_1927_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v_x_1927_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v_x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 0);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg___boxed(lean_object* v_x_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(size_t v_sz_1948_, size_t v_i_1949_, lean_object* v_bs_1950_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_usize_dec_lt(v_i_1949_, v_sz_1948_);
if (v___x_1951_ == 0)
{
return v_bs_1950_;
}
else
{
lean_object* v_v_1952_; lean_object* v_msg_1953_; lean_object* v___x_1954_; lean_object* v_bs_x27_1955_; size_t v___x_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
v_v_1952_ = lean_array_uget_borrowed(v_bs_1950_, v_i_1949_);
v_msg_1953_ = lean_ctor_get(v_v_1952_, 1);
lean_inc_ref(v_msg_1953_);
v___x_1954_ = lean_unsigned_to_nat(0u);
v_bs_x27_1955_ = lean_array_uset(v_bs_1950_, v_i_1949_, v___x_1954_);
v___x_1956_ = ((size_t)1ULL);
v___x_1957_ = lean_usize_add(v_i_1949_, v___x_1956_);
v___x_1958_ = lean_array_uset(v_bs_x27_1955_, v_i_1949_, v_msg_1953_);
v_i_1949_ = v___x_1957_;
v_bs_1950_ = v___x_1958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1960_, lean_object* v_i_1961_, lean_object* v_bs_1962_){
_start:
{
size_t v_sz_boxed_1963_; size_t v_i_boxed_1964_; lean_object* v_res_1965_; 
v_sz_boxed_1963_ = lean_unbox_usize(v_sz_1960_);
lean_dec(v_sz_1960_);
v_i_boxed_1964_ = lean_unbox_usize(v_i_1961_);
lean_dec(v_i_1961_);
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_boxed_1963_, v_i_boxed_1964_, v_bs_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(lean_object* v_oldTraces_1966_, lean_object* v_data_1967_, lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_toCold_1975_; lean_object* v_currRecDepth_1976_; lean_object* v_ref_1977_; uint16_t v_optionFlags_1978_; uint8_t v_suppressElabErrors_1979_; uint8_t v_checkDeprecated_1980_; uint8_t v_isRecordingDeps_1981_; lean_object* v_ref_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_traceState_1985_; lean_object* v_traces_1986_; lean_object* v___x_1987_; size_t v_sz_1988_; size_t v___x_1989_; lean_object* v___x_1990_; lean_object* v_msg_1991_; lean_object* v___x_1992_; lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2031_; 
v_toCold_1975_ = lean_ctor_get(v___y_1972_, 0);
v_currRecDepth_1976_ = lean_ctor_get(v___y_1972_, 1);
v_ref_1977_ = lean_ctor_get(v___y_1972_, 2);
v_optionFlags_1978_ = lean_ctor_get_uint16(v___y_1972_, sizeof(void*)*3);
v_suppressElabErrors_1979_ = lean_ctor_get_uint8(v___y_1972_, sizeof(void*)*3 + 2);
v_checkDeprecated_1980_ = lean_ctor_get_uint8(v___y_1972_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1981_ = lean_ctor_get_uint8(v___y_1972_, sizeof(void*)*3 + 4);
v_ref_1982_ = l_Lean_replaceRef(v_ref_1968_, v_ref_1977_);
lean_inc(v_currRecDepth_1976_);
lean_inc_ref(v_toCold_1975_);
v___x_1983_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1983_, 0, v_toCold_1975_);
lean_ctor_set(v___x_1983_, 1, v_currRecDepth_1976_);
lean_ctor_set(v___x_1983_, 2, v_ref_1982_);
lean_ctor_set_uint16(v___x_1983_, sizeof(void*)*3, v_optionFlags_1978_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*3 + 2, v_suppressElabErrors_1979_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*3 + 3, v_checkDeprecated_1980_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*3 + 4, v_isRecordingDeps_1981_);
v___x_1984_ = lean_st_ref_get(v___y_1973_);
v_traceState_1985_ = lean_ctor_get(v___x_1984_, 4);
lean_inc_ref(v_traceState_1985_);
lean_dec(v___x_1984_);
v_traces_1986_ = lean_ctor_get(v_traceState_1985_, 0);
lean_inc_ref(v_traces_1986_);
lean_dec_ref(v_traceState_1985_);
v___x_1987_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1986_);
lean_dec_ref(v_traces_1986_);
v_sz_1988_ = lean_array_size(v___x_1987_);
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_1988_, v___x_1989_, v___x_1987_);
v_msg_1991_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1991_, 0, v_data_1967_);
lean_ctor_set(v_msg_1991_, 1, v_msg_1969_);
lean_ctor_set(v_msg_1991_, 2, v___x_1990_);
v___x_1992_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1991_, v___y_1970_, v___y_1971_, v___x_1983_, v___y_1973_);
lean_dec_ref_known(v___x_1983_, 3);
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2031_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2031_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v_traceState_1998_; lean_object* v_env_1999_; lean_object* v_nextMacroScope_2000_; lean_object* v_ngen_2001_; lean_object* v_auxDeclNGen_2002_; lean_object* v_cache_2003_; lean_object* v_recordedDeps_2004_; lean_object* v_messages_2005_; lean_object* v_infoState_2006_; lean_object* v_snapshotTasks_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2030_; 
v___x_1997_ = lean_st_ref_take(v___y_1973_);
v_traceState_1998_ = lean_ctor_get(v___x_1997_, 4);
v_env_1999_ = lean_ctor_get(v___x_1997_, 0);
v_nextMacroScope_2000_ = lean_ctor_get(v___x_1997_, 1);
v_ngen_2001_ = lean_ctor_get(v___x_1997_, 2);
v_auxDeclNGen_2002_ = lean_ctor_get(v___x_1997_, 3);
v_cache_2003_ = lean_ctor_get(v___x_1997_, 5);
v_recordedDeps_2004_ = lean_ctor_get(v___x_1997_, 6);
v_messages_2005_ = lean_ctor_get(v___x_1997_, 7);
v_infoState_2006_ = lean_ctor_get(v___x_1997_, 8);
v_snapshotTasks_2007_ = lean_ctor_get(v___x_1997_, 9);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2009_ = v___x_1997_;
v_isShared_2010_ = v_isSharedCheck_2030_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snapshotTasks_2007_);
lean_inc(v_infoState_2006_);
lean_inc(v_messages_2005_);
lean_inc(v_recordedDeps_2004_);
lean_inc(v_cache_2003_);
lean_inc(v_traceState_1998_);
lean_inc(v_auxDeclNGen_2002_);
lean_inc(v_ngen_2001_);
lean_inc(v_nextMacroScope_2000_);
lean_inc(v_env_1999_);
lean_dec(v___x_1997_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2030_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
uint64_t v_tid_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2028_; 
v_tid_2011_ = lean_ctor_get_uint64(v_traceState_1998_, sizeof(void*)*1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_traceState_1998_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v_traceState_1998_, 0);
lean_dec(v_unused_2029_);
v___x_2013_ = v_traceState_1998_;
v_isShared_2014_ = v_isSharedCheck_2028_;
goto v_resetjp_2012_;
}
else
{
lean_dec(v_traceState_1998_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2028_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_ref_1968_);
lean_ctor_set(v___x_2016_, 1, v_a_1993_);
v___x_2017_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1966_, v___x_2016_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2017_);
v___x_2019_ = v___x_2013_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2017_);
lean_ctor_set_uint64(v_reuseFailAlloc_2027_, sizeof(void*)*1, v_tid_2011_);
v___x_2019_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___x_2019_);
v___x_2021_ = v___x_2009_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_env_1999_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_nextMacroScope_2000_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_ngen_2001_);
lean_ctor_set(v_reuseFailAlloc_2026_, 3, v_auxDeclNGen_2002_);
lean_ctor_set(v_reuseFailAlloc_2026_, 4, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2026_, 5, v_cache_2003_);
lean_ctor_set(v_reuseFailAlloc_2026_, 6, v_recordedDeps_2004_);
lean_ctor_set(v_reuseFailAlloc_2026_, 7, v_messages_2005_);
lean_ctor_set(v_reuseFailAlloc_2026_, 8, v_infoState_2006_);
lean_ctor_set(v_reuseFailAlloc_2026_, 9, v_snapshotTasks_2007_);
v___x_2021_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_st_ref_put(v___y_1973_, v___x_2021_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2015_);
v___x_2024_ = v___x_1995_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2015_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg___boxed(lean_object* v_oldTraces_2032_, lean_object* v_data_2033_, lean_object* v_ref_2034_, lean_object* v_msg_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2032_, v_data_2033_, v_ref_2034_, v_msg_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2041_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0));
v___x_2044_ = l_Lean_stringToMessageData(v___x_2043_);
return v___x_2044_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2045_; double v___x_2046_; 
v___x_2045_ = lean_unsigned_to_nat(1000u);
v___x_2046_ = lean_float_of_nat(v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object* v_cls_2047_, uint8_t v_collapsed_2048_, lean_object* v_tag_2049_, lean_object* v_opts_2050_, uint8_t v_clsEnabled_2051_, lean_object* v_oldTraces_2052_, lean_object* v_msg_2053_, lean_object* v_resStartStop_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_fst_2062_; lean_object* v_snd_2063_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v_data_2067_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___y_2075_; lean_object* v_a_2076_; uint8_t v___y_2091_; double v___y_2123_; 
v_fst_2062_ = lean_ctor_get(v_resStartStop_2054_, 0);
lean_inc(v_fst_2062_);
v_snd_2063_ = lean_ctor_get(v_resStartStop_2054_, 1);
lean_inc(v_snd_2063_);
lean_dec_ref(v_resStartStop_2054_);
v_fst_2070_ = lean_ctor_get(v_snd_2063_, 0);
lean_inc(v_fst_2070_);
v_snd_2071_ = lean_ctor_get(v_snd_2063_, 1);
lean_inc(v_snd_2071_);
lean_dec(v_snd_2063_);
v___x_2072_ = l_Lean_trace_profiler;
v___x_2073_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2050_, v___x_2072_);
if (v___x_2073_ == 0)
{
v___y_2091_ = v___x_2073_;
goto v___jp_2090_;
}
else
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2129_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2050_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; double v___x_2132_; double v___x_2133_; double v___x_2134_; 
v___x_2130_ = l_Lean_trace_profiler_threshold;
v___x_2131_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2050_, v___x_2130_);
v___x_2132_ = lean_float_of_nat(v___x_2131_);
v___x_2133_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_2134_ = lean_float_div(v___x_2132_, v___x_2133_);
v___y_2123_ = v___x_2134_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; double v___x_2137_; 
v___x_2135_ = l_Lean_trace_profiler_threshold;
v___x_2136_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2050_, v___x_2135_);
v___x_2137_ = lean_float_of_nat(v___x_2136_);
v___y_2123_ = v___x_2137_;
goto v___jp_2122_;
}
}
v___jp_2064_:
{
lean_object* v___x_2068_; 
lean_inc(v___y_2065_);
v___x_2068_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2052_, v_data_2067_, v___y_2065_, v___y_2066_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref_known(v___x_2068_, 1);
v___x_2069_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2062_);
return v___x_2069_;
}
else
{
lean_dec(v_fst_2062_);
return v___x_2068_;
}
}
v___jp_2074_:
{
uint8_t v_result_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; double v___x_2080_; lean_object* v_data_2081_; 
v_result_2077_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_fst_2062_);
v___x_2078_ = lean_box(v_result_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
v___x_2080_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2049_);
lean_inc_ref(v___x_2079_);
lean_inc(v_cls_2047_);
v_data_2081_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2081_, 0, v_cls_2047_);
lean_ctor_set(v_data_2081_, 1, v___x_2079_);
lean_ctor_set(v_data_2081_, 2, v_tag_2049_);
lean_ctor_set_float(v_data_2081_, sizeof(void*)*3, v___x_2080_);
lean_ctor_set_float(v_data_2081_, sizeof(void*)*3 + 8, v___x_2080_);
lean_ctor_set_uint8(v_data_2081_, sizeof(void*)*3 + 16, v_collapsed_2048_);
if (v___x_2073_ == 0)
{
lean_dec_ref_known(v___x_2079_, 1);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2070_);
lean_dec_ref(v_tag_2049_);
lean_dec(v_cls_2047_);
v___y_2065_ = v___y_2075_;
v___y_2066_ = v_a_2076_;
v_data_2067_ = v_data_2081_;
goto v___jp_2064_;
}
else
{
lean_object* v_data_2082_; double v___x_2083_; double v___x_2084_; 
lean_dec_ref_known(v_data_2081_, 3);
v_data_2082_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2082_, 0, v_cls_2047_);
lean_ctor_set(v_data_2082_, 1, v___x_2079_);
lean_ctor_set(v_data_2082_, 2, v_tag_2049_);
v___x_2083_ = lean_unbox_float(v_fst_2070_);
lean_dec(v_fst_2070_);
lean_ctor_set_float(v_data_2082_, sizeof(void*)*3, v___x_2083_);
v___x_2084_ = lean_unbox_float(v_snd_2071_);
lean_dec(v_snd_2071_);
lean_ctor_set_float(v_data_2082_, sizeof(void*)*3 + 8, v___x_2084_);
lean_ctor_set_uint8(v_data_2082_, sizeof(void*)*3 + 16, v_collapsed_2048_);
v___y_2065_ = v___y_2075_;
v___y_2066_ = v_a_2076_;
v_data_2067_ = v_data_2082_;
goto v___jp_2064_;
}
}
v___jp_2085_:
{
lean_object* v_ref_2086_; lean_object* v___x_2087_; 
v_ref_2086_ = lean_ctor_get(v___y_2059_, 2);
lean_inc(v___y_2060_);
lean_inc_ref(v___y_2059_);
lean_inc(v___y_2058_);
lean_inc_ref(v___y_2057_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2055_);
lean_inc(v_fst_2062_);
v___x_2087_ = lean_apply_8(v_msg_2053_, v_fst_2062_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, lean_box(0));
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___y_2075_ = v_ref_2086_;
v_a_2076_ = v_a_2088_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_2075_ = v_ref_2086_;
v_a_2076_ = v___x_2089_;
goto v___jp_2074_;
}
}
v___jp_2090_:
{
if (v_clsEnabled_2051_ == 0)
{
if (v___y_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v_traceState_2093_; lean_object* v_env_2094_; lean_object* v_nextMacroScope_2095_; lean_object* v_ngen_2096_; lean_object* v_auxDeclNGen_2097_; lean_object* v_cache_2098_; lean_object* v_recordedDeps_2099_; lean_object* v_messages_2100_; lean_object* v_infoState_2101_; lean_object* v_snapshotTasks_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_snd_2071_);
lean_dec(v_fst_2070_);
lean_dec_ref(v_msg_2053_);
lean_dec_ref(v_tag_2049_);
lean_dec(v_cls_2047_);
v___x_2092_ = lean_st_ref_take(v___y_2060_);
v_traceState_2093_ = lean_ctor_get(v___x_2092_, 4);
v_env_2094_ = lean_ctor_get(v___x_2092_, 0);
v_nextMacroScope_2095_ = lean_ctor_get(v___x_2092_, 1);
v_ngen_2096_ = lean_ctor_get(v___x_2092_, 2);
v_auxDeclNGen_2097_ = lean_ctor_get(v___x_2092_, 3);
v_cache_2098_ = lean_ctor_get(v___x_2092_, 5);
v_recordedDeps_2099_ = lean_ctor_get(v___x_2092_, 6);
v_messages_2100_ = lean_ctor_get(v___x_2092_, 7);
v_infoState_2101_ = lean_ctor_get(v___x_2092_, 8);
v_snapshotTasks_2102_ = lean_ctor_get(v___x_2092_, 9);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2104_ = v___x_2092_;
v_isShared_2105_ = v_isSharedCheck_2121_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snapshotTasks_2102_);
lean_inc(v_infoState_2101_);
lean_inc(v_messages_2100_);
lean_inc(v_recordedDeps_2099_);
lean_inc(v_cache_2098_);
lean_inc(v_traceState_2093_);
lean_inc(v_auxDeclNGen_2097_);
lean_inc(v_ngen_2096_);
lean_inc(v_nextMacroScope_2095_);
lean_inc(v_env_2094_);
lean_dec(v___x_2092_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2121_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
uint64_t v_tid_2106_; lean_object* v_traces_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2120_; 
v_tid_2106_ = lean_ctor_get_uint64(v_traceState_2093_, sizeof(void*)*1);
v_traces_2107_ = lean_ctor_get(v_traceState_2093_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_traceState_2093_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2109_ = v_traceState_2093_;
v_isShared_2110_ = v_isSharedCheck_2120_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_traces_2107_);
lean_dec(v_traceState_2093_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2120_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2052_, v_traces_2107_);
lean_dec_ref(v_traces_2107_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2111_);
lean_ctor_set_uint64(v_reuseFailAlloc_2119_, sizeof(void*)*1, v_tid_2106_);
v___x_2113_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 4, v___x_2113_);
v___x_2115_ = v___x_2104_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_env_2094_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_nextMacroScope_2095_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_ngen_2096_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_auxDeclNGen_2097_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2118_, 5, v_cache_2098_);
lean_ctor_set(v_reuseFailAlloc_2118_, 6, v_recordedDeps_2099_);
lean_ctor_set(v_reuseFailAlloc_2118_, 7, v_messages_2100_);
lean_ctor_set(v_reuseFailAlloc_2118_, 8, v_infoState_2101_);
lean_ctor_set(v_reuseFailAlloc_2118_, 9, v_snapshotTasks_2102_);
v___x_2115_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_st_ref_put(v___y_2060_, v___x_2115_);
v___x_2117_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2062_);
return v___x_2117_;
}
}
}
}
}
else
{
goto v___jp_2085_;
}
}
else
{
goto v___jp_2085_;
}
}
v___jp_2122_:
{
double v___x_2124_; double v___x_2125_; double v___x_2126_; uint8_t v___x_2127_; 
v___x_2124_ = lean_unbox_float(v_snd_2071_);
v___x_2125_ = lean_unbox_float(v_fst_2070_);
v___x_2126_ = lean_float_sub(v___x_2124_, v___x_2125_);
v___x_2127_ = lean_float_decLt(v___y_2123_, v___x_2126_);
v___y_2091_ = v___x_2127_;
goto v___jp_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object* v_cls_2138_, lean_object* v_collapsed_2139_, lean_object* v_tag_2140_, lean_object* v_opts_2141_, lean_object* v_clsEnabled_2142_, lean_object* v_oldTraces_2143_, lean_object* v_msg_2144_, lean_object* v_resStartStop_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v_collapsed_boxed_2153_; uint8_t v_clsEnabled_boxed_2154_; lean_object* v_res_2155_; 
v_collapsed_boxed_2153_ = lean_unbox(v_collapsed_2139_);
v_clsEnabled_boxed_2154_ = lean_unbox(v_clsEnabled_2142_);
v_res_2155_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_cls_2138_, v_collapsed_boxed_2153_, v_tag_2140_, v_opts_2141_, v_clsEnabled_boxed_2154_, v_oldTraces_2143_, v_msg_2144_, v_resStartStop_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec_ref(v_opts_2141_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
lean_object* v_ks_2160_; lean_object* v_vs_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2185_; 
v_ks_2160_ = lean_ctor_get(v_x_2156_, 0);
v_vs_2161_ = lean_ctor_get(v_x_2156_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_x_2156_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2163_ = v_x_2156_;
v_isShared_2164_ = v_isSharedCheck_2185_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_vs_2161_);
lean_inc(v_ks_2160_);
lean_dec(v_x_2156_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2185_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_array_get_size(v_ks_2160_);
v___x_2166_ = lean_nat_dec_lt(v_x_2157_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec(v_x_2157_);
v___x_2167_ = lean_array_push(v_ks_2160_, v_x_2158_);
v___x_2168_ = lean_array_push(v_vs_2161_, v_x_2159_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2168_);
lean_ctor_set(v___x_2163_, 0, v___x_2167_);
v___x_2170_ = v___x_2163_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
else
{
lean_object* v_k_x27_2172_; uint8_t v___x_2173_; 
v_k_x27_2172_ = lean_array_fget_borrowed(v_ks_2160_, v_x_2157_);
v___x_2173_ = l_Lean_instBEqMVarId_beq(v_x_2158_, v_k_x27_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2175_; 
if (v_isShared_2164_ == 0)
{
v___x_2175_ = v___x_2163_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_ks_2160_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_vs_2161_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_add(v_x_2157_, v___x_2176_);
lean_dec(v_x_2157_);
v_x_2156_ = v___x_2175_;
v_x_2157_ = v___x_2177_;
goto _start;
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = lean_array_fset(v_ks_2160_, v_x_2157_, v_x_2158_);
v___x_2181_ = lean_array_fset(v_vs_2161_, v_x_2157_, v_x_2159_);
lean_dec(v_x_2157_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2181_);
lean_ctor_set(v___x_2163_, 0, v___x_2180_);
v___x_2183_ = v___x_2163_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_n_2186_, lean_object* v_k_2187_, lean_object* v_v_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_n_2186_, v___x_2189_, v_k_2187_, v_v_2188_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2192_, size_t v_x_2193_, size_t v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
lean_object* v_es_2197_; size_t v___x_2198_; size_t v___x_2199_; lean_object* v_j_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v_es_2197_ = lean_ctor_get(v_x_2192_, 0);
v___x_2198_ = ((size_t)31ULL);
v___x_2199_ = lean_usize_land(v_x_2193_, v___x_2198_);
v_j_2200_ = lean_usize_to_nat(v___x_2199_);
v___x_2201_ = lean_array_get_size(v_es_2197_);
v___x_2202_ = lean_nat_dec_lt(v_j_2200_, v___x_2201_);
if (v___x_2202_ == 0)
{
lean_dec(v_j_2200_);
lean_dec(v_x_2196_);
lean_dec(v_x_2195_);
return v_x_2192_;
}
else
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2241_; 
lean_inc_ref(v_es_2197_);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v_x_2192_, 0);
lean_dec(v_unused_2242_);
v___x_2204_ = v_x_2192_;
v_isShared_2205_ = v_isSharedCheck_2241_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v_x_2192_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2241_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_v_2206_; lean_object* v___x_2207_; lean_object* v_xs_x27_2208_; lean_object* v___y_2210_; 
v_v_2206_ = lean_array_fget(v_es_2197_, v_j_2200_);
v___x_2207_ = lean_box(0);
v_xs_x27_2208_ = lean_array_fset(v_es_2197_, v_j_2200_, v___x_2207_);
switch(lean_obj_tag(v_v_2206_))
{
case 0:
{
lean_object* v_key_2215_; lean_object* v_val_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2226_; 
v_key_2215_ = lean_ctor_get(v_v_2206_, 0);
v_val_2216_ = lean_ctor_get(v_v_2206_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_v_2206_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2218_ = v_v_2206_;
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_val_2216_);
lean_inc(v_key_2215_);
lean_dec(v_v_2206_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Lean_instBEqMVarId_beq(v_x_2195_, v_key_2215_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_del_object(v___x_2218_);
v___x_2221_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2215_, v_val_2216_, v_x_2195_, v_x_2196_);
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
v___y_2210_ = v___x_2222_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2224_; 
lean_dec(v_val_2216_);
lean_dec(v_key_2215_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_x_2196_);
lean_ctor_set(v___x_2218_, 0, v_x_2195_);
v___x_2224_ = v___x_2218_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_x_2195_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_x_2196_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
v___y_2210_ = v___x_2224_;
goto v___jp_2209_;
}
}
}
}
case 1:
{
lean_object* v_node_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2239_; 
v_node_2227_ = lean_ctor_get(v_v_2206_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_v_2206_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2229_ = v_v_2206_;
v_isShared_2230_ = v_isSharedCheck_2239_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_node_2227_);
lean_dec(v_v_2206_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2239_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
size_t v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2231_ = ((size_t)5ULL);
v___x_2232_ = lean_usize_shift_right(v_x_2193_, v___x_2231_);
v___x_2233_ = ((size_t)1ULL);
v___x_2234_ = lean_usize_add(v_x_2194_, v___x_2233_);
v___x_2235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_node_2227_, v___x_2232_, v___x_2234_, v_x_2195_, v_x_2196_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2235_);
v___x_2237_ = v___x_2229_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
v___y_2210_ = v___x_2237_;
goto v___jp_2209_;
}
}
}
default: 
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_x_2195_);
lean_ctor_set(v___x_2240_, 1, v_x_2196_);
v___y_2210_ = v___x_2240_;
goto v___jp_2209_;
}
}
v___jp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_array_fset(v_xs_x27_2208_, v_j_2200_, v___y_2210_);
lean_dec(v_j_2200_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2211_);
v___x_2213_ = v___x_2204_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
else
{
lean_object* v_ks_2243_; lean_object* v_vs_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2262_; 
v_ks_2243_ = lean_ctor_get(v_x_2192_, 0);
v_vs_2244_ = lean_ctor_get(v_x_2192_, 1);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2246_ = v_x_2192_;
v_isShared_2247_ = v_isSharedCheck_2262_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_vs_2244_);
lean_inc(v_ks_2243_);
lean_dec(v_x_2192_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2262_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_ks_2243_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_vs_2244_);
v___x_2249_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v_newNode_2250_; size_t v___x_2251_; uint8_t v___x_2252_; 
v_newNode_2250_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v___x_2249_, v_x_2195_, v_x_2196_);
v___x_2251_ = ((size_t)7ULL);
v___x_2252_ = lean_usize_dec_le(v___x_2251_, v_x_2194_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2253_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2250_);
v___x_2254_ = lean_unsigned_to_nat(4u);
v___x_2255_ = lean_nat_dec_lt(v___x_2253_, v___x_2254_);
lean_dec(v___x_2253_);
if (v___x_2255_ == 0)
{
lean_object* v_ks_2256_; lean_object* v_vs_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_ks_2256_ = lean_ctor_get(v_newNode_2250_, 0);
lean_inc_ref(v_ks_2256_);
v_vs_2257_ = lean_ctor_get(v_newNode_2250_, 1);
lean_inc_ref(v_vs_2257_);
lean_dec_ref(v_newNode_2250_);
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_2260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_x_2194_, v_ks_2256_, v_vs_2257_, v___x_2258_, v___x_2259_);
lean_dec_ref(v_vs_2257_);
lean_dec_ref(v_ks_2256_);
return v___x_2260_;
}
else
{
return v_newNode_2250_;
}
}
else
{
return v_newNode_2250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t v_depth_2263_, lean_object* v_keys_2264_, lean_object* v_vals_2265_, lean_object* v_i_2266_, lean_object* v_entries_2267_){
_start:
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = lean_array_get_size(v_keys_2264_);
v___x_2269_ = lean_nat_dec_lt(v_i_2266_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec(v_i_2266_);
return v_entries_2267_;
}
else
{
lean_object* v_k_2270_; lean_object* v_v_2271_; uint64_t v___x_2272_; size_t v_h_2273_; size_t v___x_2274_; lean_object* v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; size_t v_h_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v_k_2270_ = lean_array_fget_borrowed(v_keys_2264_, v_i_2266_);
v_v_2271_ = lean_array_fget_borrowed(v_vals_2265_, v_i_2266_);
v___x_2272_ = l_Lean_instHashableMVarId_hash(v_k_2270_);
v_h_2273_ = lean_uint64_to_usize(v___x_2272_);
v___x_2274_ = ((size_t)5ULL);
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = ((size_t)1ULL);
v___x_2277_ = lean_usize_sub(v_depth_2263_, v___x_2276_);
v___x_2278_ = lean_usize_mul(v___x_2274_, v___x_2277_);
v_h_2279_ = lean_usize_shift_right(v_h_2273_, v___x_2278_);
v___x_2280_ = lean_nat_add(v_i_2266_, v___x_2275_);
lean_dec(v_i_2266_);
lean_inc(v_v_2271_);
lean_inc(v_k_2270_);
v___x_2281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_entries_2267_, v_h_2279_, v_depth_2263_, v_k_2270_, v_v_2271_);
v_i_2266_ = v___x_2280_;
v_entries_2267_ = v___x_2281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_depth_2283_, lean_object* v_keys_2284_, lean_object* v_vals_2285_, lean_object* v_i_2286_, lean_object* v_entries_2287_){
_start:
{
size_t v_depth_boxed_2288_; lean_object* v_res_2289_; 
v_depth_boxed_2288_ = lean_unbox_usize(v_depth_2283_);
lean_dec(v_depth_2283_);
v_res_2289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_boxed_2288_, v_keys_2284_, v_vals_2285_, v_i_2286_, v_entries_2287_);
lean_dec_ref(v_vals_2285_);
lean_dec_ref(v_keys_2284_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_){
_start:
{
size_t v_x_17304__boxed_2295_; size_t v_x_17305__boxed_2296_; lean_object* v_res_2297_; 
v_x_17304__boxed_2295_ = lean_unbox_usize(v_x_2291_);
lean_dec(v_x_2291_);
v_x_17305__boxed_2296_ = lean_unbox_usize(v_x_2292_);
lean_dec(v_x_2292_);
v_res_2297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2290_, v_x_17304__boxed_2295_, v_x_17305__boxed_2296_, v_x_2293_, v_x_2294_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object* v_x_2298_, lean_object* v_x_2299_, lean_object* v_x_2300_){
_start:
{
uint64_t v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; 
v___x_2301_ = l_Lean_instHashableMVarId_hash(v_x_2299_);
v___x_2302_ = lean_uint64_to_usize(v___x_2301_);
v___x_2303_ = ((size_t)1ULL);
v___x_2304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2298_, v___x_2302_, v___x_2303_, v_x_2299_, v_x_2300_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v_mvarId_2305_, lean_object* v_val_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v_mctx_2310_; lean_object* v_cache_2311_; lean_object* v_zetaDeltaFVarIds_2312_; lean_object* v_postponed_2313_; lean_object* v_diag_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2344_; 
v___x_2309_ = lean_st_ref_take(v___y_2307_);
v_mctx_2310_ = lean_ctor_get(v___x_2309_, 0);
v_cache_2311_ = lean_ctor_get(v___x_2309_, 1);
v_zetaDeltaFVarIds_2312_ = lean_ctor_get(v___x_2309_, 2);
v_postponed_2313_ = lean_ctor_get(v___x_2309_, 3);
v_diag_2314_ = lean_ctor_get(v___x_2309_, 4);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2316_ = v___x_2309_;
v_isShared_2317_ = v_isSharedCheck_2344_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_diag_2314_);
lean_inc(v_postponed_2313_);
lean_inc(v_zetaDeltaFVarIds_2312_);
lean_inc(v_cache_2311_);
lean_inc(v_mctx_2310_);
lean_dec(v___x_2309_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2344_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_depth_2318_; lean_object* v_levelAssignDepth_2319_; lean_object* v_lmvarCounter_2320_; lean_object* v_mvarCounter_2321_; lean_object* v_lDecls_2322_; lean_object* v_decls_2323_; lean_object* v_userNames_2324_; lean_object* v_lAssignment_2325_; lean_object* v_eAssignment_2326_; lean_object* v_dAssignment_2327_; lean_object* v_instanceTypedMVars_2328_; lean_object* v_synthNormMemo_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2343_; 
v_depth_2318_ = lean_ctor_get(v_mctx_2310_, 0);
v_levelAssignDepth_2319_ = lean_ctor_get(v_mctx_2310_, 1);
v_lmvarCounter_2320_ = lean_ctor_get(v_mctx_2310_, 2);
v_mvarCounter_2321_ = lean_ctor_get(v_mctx_2310_, 3);
v_lDecls_2322_ = lean_ctor_get(v_mctx_2310_, 4);
v_decls_2323_ = lean_ctor_get(v_mctx_2310_, 5);
v_userNames_2324_ = lean_ctor_get(v_mctx_2310_, 6);
v_lAssignment_2325_ = lean_ctor_get(v_mctx_2310_, 7);
v_eAssignment_2326_ = lean_ctor_get(v_mctx_2310_, 8);
v_dAssignment_2327_ = lean_ctor_get(v_mctx_2310_, 9);
v_instanceTypedMVars_2328_ = lean_ctor_get(v_mctx_2310_, 10);
v_synthNormMemo_2329_ = lean_ctor_get(v_mctx_2310_, 11);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_mctx_2310_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2331_ = v_mctx_2310_;
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_synthNormMemo_2329_);
lean_inc(v_instanceTypedMVars_2328_);
lean_inc(v_dAssignment_2327_);
lean_inc(v_eAssignment_2326_);
lean_inc(v_lAssignment_2325_);
lean_inc(v_userNames_2324_);
lean_inc(v_decls_2323_);
lean_inc(v_lDecls_2322_);
lean_inc(v_mvarCounter_2321_);
lean_inc(v_lmvarCounter_2320_);
lean_inc(v_levelAssignDepth_2319_);
lean_inc(v_depth_2318_);
lean_dec(v_mctx_2310_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_box(0);
v___x_2334_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_eAssignment_2326_, v_mvarId_2305_, v_val_2306_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 8, v___x_2334_);
v___x_2336_ = v___x_2331_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_depth_2318_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_levelAssignDepth_2319_);
lean_ctor_set(v_reuseFailAlloc_2342_, 2, v_lmvarCounter_2320_);
lean_ctor_set(v_reuseFailAlloc_2342_, 3, v_mvarCounter_2321_);
lean_ctor_set(v_reuseFailAlloc_2342_, 4, v_lDecls_2322_);
lean_ctor_set(v_reuseFailAlloc_2342_, 5, v_decls_2323_);
lean_ctor_set(v_reuseFailAlloc_2342_, 6, v_userNames_2324_);
lean_ctor_set(v_reuseFailAlloc_2342_, 7, v_lAssignment_2325_);
lean_ctor_set(v_reuseFailAlloc_2342_, 8, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2342_, 9, v_dAssignment_2327_);
lean_ctor_set(v_reuseFailAlloc_2342_, 10, v_instanceTypedMVars_2328_);
lean_ctor_set(v_reuseFailAlloc_2342_, 11, v_synthNormMemo_2329_);
v___x_2336_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2336_);
v___x_2338_ = v___x_2316_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_cache_2311_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_zetaDeltaFVarIds_2312_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_postponed_2313_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_diag_2314_);
v___x_2338_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_st_ref_put(v___y_2307_, v___x_2338_);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2333_);
return v___x_2340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object* v_mvarId_2345_, lean_object* v_val_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2345_, v_val_2346_, v___y_2347_);
lean_dec(v___y_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_keys_2350_, lean_object* v_i_2351_, lean_object* v_k_2352_){
_start:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = lean_array_get_size(v_keys_2350_);
v___x_2354_ = lean_nat_dec_lt(v_i_2351_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_dec(v_i_2351_);
return v___x_2354_;
}
else
{
lean_object* v_k_x27_2355_; uint8_t v___x_2356_; 
v_k_x27_2355_ = lean_array_fget_borrowed(v_keys_2350_, v_i_2351_);
v___x_2356_ = l_Lean_instBEqMVarId_beq(v_k_2352_, v_k_x27_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_add(v_i_2351_, v___x_2357_);
lean_dec(v_i_2351_);
v_i_2351_ = v___x_2358_;
goto _start;
}
else
{
lean_dec(v_i_2351_);
return v___x_2354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_keys_2360_, lean_object* v_i_2361_, lean_object* v_k_2362_){
_start:
{
uint8_t v_res_2363_; lean_object* v_r_2364_; 
v_res_2363_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2360_, v_i_2361_, v_k_2362_);
lean_dec(v_k_2362_);
lean_dec_ref(v_keys_2360_);
v_r_2364_ = lean_box(v_res_2363_);
return v_r_2364_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(lean_object* v_x_2365_, size_t v_x_2366_, lean_object* v_x_2367_){
_start:
{
if (lean_obj_tag(v_x_2365_) == 0)
{
lean_object* v_es_2368_; lean_object* v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; lean_object* v_j_2372_; lean_object* v___x_2373_; 
v_es_2368_ = lean_ctor_get(v_x_2365_, 0);
v___x_2369_ = lean_box(2);
v___x_2370_ = ((size_t)31ULL);
v___x_2371_ = lean_usize_land(v_x_2366_, v___x_2370_);
v_j_2372_ = lean_usize_to_nat(v___x_2371_);
v___x_2373_ = lean_array_get_borrowed(v___x_2369_, v_es_2368_, v_j_2372_);
lean_dec(v_j_2372_);
switch(lean_obj_tag(v___x_2373_))
{
case 0:
{
lean_object* v_key_2374_; uint8_t v___x_2375_; 
v_key_2374_ = lean_ctor_get(v___x_2373_, 0);
v___x_2375_ = l_Lean_instBEqMVarId_beq(v_x_2367_, v_key_2374_);
return v___x_2375_;
}
case 1:
{
lean_object* v_node_2376_; size_t v___x_2377_; size_t v___x_2378_; 
v_node_2376_ = lean_ctor_get(v___x_2373_, 0);
v___x_2377_ = ((size_t)5ULL);
v___x_2378_ = lean_usize_shift_right(v_x_2366_, v___x_2377_);
v_x_2365_ = v_node_2376_;
v_x_2366_ = v___x_2378_;
goto _start;
}
default: 
{
uint8_t v___x_2380_; 
v___x_2380_ = 0;
return v___x_2380_;
}
}
}
else
{
lean_object* v_ks_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v_ks_2381_ = lean_ctor_get(v_x_2365_, 0);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_ks_2381_, v___x_2382_, v_x_2367_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_){
_start:
{
size_t v_x_17526__boxed_2387_; uint8_t v_res_2388_; lean_object* v_r_2389_; 
v_x_17526__boxed_2387_ = lean_unbox_usize(v_x_2385_);
lean_dec(v_x_2385_);
v_res_2388_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2384_, v_x_17526__boxed_2387_, v_x_2386_);
lean_dec(v_x_2386_);
lean_dec_ref(v_x_2384_);
v_r_2389_ = lean_box(v_res_2388_);
return v_r_2389_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
uint64_t v___x_2392_; size_t v___x_2393_; uint8_t v___x_2394_; 
v___x_2392_ = l_Lean_instHashableMVarId_hash(v_x_2391_);
v___x_2393_ = lean_uint64_to_usize(v___x_2392_);
v___x_2394_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2390_, v___x_2393_, v_x_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg___boxed(lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_res_2397_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2395_, v_x_2396_);
lean_dec(v_x_2396_);
lean_dec_ref(v_x_2395_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(lean_object* v_mvarId_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v_mctx_2403_; lean_object* v_eAssignment_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2402_ = lean_st_ref_get(v___y_2400_);
v_mctx_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc_ref(v_mctx_2403_);
lean_dec(v___x_2402_);
v_eAssignment_2404_ = lean_ctor_get(v_mctx_2403_, 8);
lean_inc_ref(v_eAssignment_2404_);
lean_dec_ref(v_mctx_2403_);
v___x_2405_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_eAssignment_2404_, v_mvarId_2399_);
lean_dec_ref(v_eAssignment_2404_);
v___x_2406_ = lean_box(v___x_2405_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg___boxed(lean_object* v_mvarId_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec(v_mvarId_2408_);
return v_res_2411_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2412_; double v___x_2413_; 
v___x_2412_ = lean_unsigned_to_nat(1000000000u);
v___x_2413_ = lean_float_of_nat(v___x_2412_);
return v___x_2413_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1));
v___x_2416_ = l_Lean_stringToMessageData(v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(lean_object* v___x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v___x_2417_, v___y_2421_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2591_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2591_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2591_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_unbox(v_a_2426_);
lean_dec(v_a_2426_);
if (v___x_2430_ == 0)
{
uint8_t v___x_2431_; lean_object* v___x_2432_; 
lean_del_object(v___x_2428_);
v___x_2431_ = 1;
lean_inc(v___x_2417_);
v___x_2432_ = l_Lean_MVarId_getType(v___x_2417_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_toCold_2433_; lean_object* v_options_2434_; uint8_t v_hasTrace_2435_; 
v_toCold_2433_ = lean_ctor_get(v___y_2422_, 0);
v_options_2434_ = lean_ctor_get(v_toCold_2433_, 2);
v_hasTrace_2435_ = lean_ctor_get_uint8(v_options_2434_, sizeof(void*)*1);
if (v_hasTrace_2435_ == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2437_ = l_Lean_Meta_mkDefault(v_a_2436_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2438_, v___y_2421_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2447_; 
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v___x_2439_, 0);
lean_dec(v_unused_2448_);
v___x_2441_ = v___x_2439_;
v_isShared_2442_ = v_isSharedCheck_2447_;
goto v_resetjp_2440_;
}
else
{
lean_dec(v___x_2439_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2447_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2443_ = lean_box(0);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2443_);
v___x_2445_ = v___x_2441_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
return v___x_2439_;
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v___x_2417_);
v_a_2449_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2437_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2437_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v_inheritedTraceOptions_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v_a_2467_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v_a_2482_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v_a_2487_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v_a_2492_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v_a_2504_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v_a_2509_; 
v_a_2457_ = lean_ctor_get(v___x_2432_, 0);
lean_inc_n(v_a_2457_, 2);
lean_dec_ref_known(v___x_2432_, 1);
v_inheritedTraceOptions_2458_ = lean_ctor_get(v_toCold_2433_, 11);
v___f_2459_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2459_, 0, v_a_2457_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2461_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_2462_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2463_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2458_, v_options_2434_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = l_Lean_trace_profiler;
v___x_2553_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2434_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref(v___f_2459_);
v___x_2554_ = l_Lean_Meta_mkDefault(v_a_2457_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_n(v_a_2555_, 2);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2555_, v___y_2421_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2569_; 
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v___x_2556_, 0);
lean_dec(v_unused_2570_);
v___x_2558_ = v___x_2556_;
v_isShared_2559_ = v_isSharedCheck_2569_;
goto v_resetjp_2557_;
}
else
{
lean_dec(v___x_2556_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2569_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
if (v___x_2463_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_dec(v_a_2555_);
v___x_2560_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_del_object(v___x_2558_);
v___x_2564_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2565_ = lean_unsigned_to_nat(30u);
v___x_2566_ = l_Lean_inlineExprTrailing(v_a_2555_, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2564_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2460_, v___x_2567_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2568_;
}
}
}
else
{
lean_dec(v_a_2555_);
return v___x_2556_;
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v___x_2417_);
v_a_2571_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2554_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2554_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
goto v___jp_2511_;
}
}
else
{
goto v___jp_2511_;
}
v___jp_2464_:
{
lean_object* v___x_2468_; double v___x_2469_; double v___x_2470_; double v___x_2471_; double v___x_2472_; double v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2468_ = lean_io_mono_nanos_now();
v___x_2469_ = lean_float_of_nat(v___y_2466_);
v___x_2470_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_2471_ = lean_float_div(v___x_2469_, v___x_2470_);
v___x_2472_ = lean_float_of_nat(v___x_2468_);
v___x_2473_ = lean_float_div(v___x_2472_, v___x_2470_);
v___x_2474_ = lean_box_float(v___x_2471_);
v___x_2475_ = lean_box_float(v___x_2473_);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v_a_2467_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2460_, v___x_2431_, v___x_2461_, v_options_2434_, v___x_2463_, v___y_2465_, v___f_2459_, v___x_2477_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2478_;
}
v___jp_2479_:
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2482_);
v___y_2465_ = v___y_2480_;
v___y_2466_ = v___y_2481_;
v_a_2467_ = v___x_2483_;
goto v___jp_2464_;
}
v___jp_2484_:
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_a_2487_);
v___y_2465_ = v___y_2485_;
v___y_2466_ = v___y_2486_;
v_a_2467_ = v___x_2488_;
goto v___jp_2464_;
}
v___jp_2489_:
{
lean_object* v___x_2493_; double v___x_2494_; double v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2493_ = lean_io_get_num_heartbeats();
v___x_2494_ = lean_float_of_nat(v___y_2491_);
v___x_2495_ = lean_float_of_nat(v___x_2493_);
v___x_2496_ = lean_box_float(v___x_2494_);
v___x_2497_ = lean_box_float(v___x_2495_);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2492_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2460_, v___x_2431_, v___x_2461_, v_options_2434_, v___x_2463_, v___y_2490_, v___f_2459_, v___x_2499_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2500_;
}
v___jp_2501_:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_a_2504_);
v___y_2490_ = v___y_2502_;
v___y_2491_ = v___y_2503_;
v_a_2492_ = v___x_2505_;
goto v___jp_2489_;
}
v___jp_2506_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_a_2509_);
v___y_2490_ = v___y_2507_;
v___y_2491_ = v___y_2508_;
v_a_2492_ = v___x_2510_;
goto v___jp_2489_;
}
v___jp_2511_:
{
lean_object* v___x_2512_; 
v___x_2512_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_2423_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2515_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2434_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_io_mono_nanos_now();
v___x_2517_ = l_Lean_Meta_mkDefault(v_a_2457_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc_n(v_a_2518_, 2);
lean_dec_ref_known(v___x_2517_, 1);
v___x_2519_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2518_, v___y_2421_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_dec_ref_known(v___x_2519_, 1);
if (v___x_2463_ == 0)
{
lean_object* v___x_2520_; 
lean_dec(v_a_2518_);
v___x_2520_ = lean_box(0);
v___y_2485_ = v_a_2513_;
v___y_2486_ = v___x_2516_;
v_a_2487_ = v___x_2520_;
goto v___jp_2484_;
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2522_ = lean_unsigned_to_nat(30u);
v___x_2523_ = l_Lean_inlineExprTrailing(v_a_2518_, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2521_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2460_, v___x_2524_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___y_2485_ = v_a_2513_;
v___y_2486_ = v___x_2516_;
v_a_2487_ = v_a_2526_;
goto v___jp_2484_;
}
else
{
lean_object* v_a_2527_; 
v_a_2527_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2525_, 1);
v___y_2480_ = v_a_2513_;
v___y_2481_ = v___x_2516_;
v_a_2482_ = v_a_2527_;
goto v___jp_2479_;
}
}
}
else
{
lean_object* v_a_2528_; 
lean_dec(v_a_2518_);
v_a_2528_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2519_, 1);
v___y_2480_ = v_a_2513_;
v___y_2481_ = v___x_2516_;
v_a_2482_ = v_a_2528_;
goto v___jp_2479_;
}
}
else
{
lean_object* v_a_2529_; 
lean_dec(v___x_2417_);
v_a_2529_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2517_, 1);
v___y_2480_ = v_a_2513_;
v___y_2481_ = v___x_2516_;
v_a_2482_ = v_a_2529_;
goto v___jp_2479_;
}
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_io_get_num_heartbeats();
v___x_2531_ = l_Lean_Meta_mkDefault(v_a_2457_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc_n(v_a_2532_, 2);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2532_, v___y_2421_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_dec_ref_known(v___x_2533_, 1);
if (v___x_2463_ == 0)
{
lean_object* v___x_2534_; 
lean_dec(v_a_2532_);
v___x_2534_ = lean_box(0);
v___y_2507_ = v_a_2513_;
v___y_2508_ = v___x_2530_;
v_a_2509_ = v___x_2534_;
goto v___jp_2506_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2536_ = lean_unsigned_to_nat(30u);
v___x_2537_ = l_Lean_inlineExprTrailing(v_a_2532_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2535_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2460_, v___x_2538_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___y_2507_ = v_a_2513_;
v___y_2508_ = v___x_2530_;
v_a_2509_ = v_a_2540_;
goto v___jp_2506_;
}
else
{
lean_object* v_a_2541_; 
v_a_2541_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2539_, 1);
v___y_2502_ = v_a_2513_;
v___y_2503_ = v___x_2530_;
v_a_2504_ = v_a_2541_;
goto v___jp_2501_;
}
}
}
else
{
lean_object* v_a_2542_; 
lean_dec(v_a_2532_);
v_a_2542_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2533_, 1);
v___y_2502_ = v_a_2513_;
v___y_2503_ = v___x_2530_;
v_a_2504_ = v_a_2542_;
goto v___jp_2501_;
}
}
else
{
lean_object* v_a_2543_; 
lean_dec(v___x_2417_);
v_a_2543_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2531_, 1);
v___y_2502_ = v_a_2513_;
v___y_2503_ = v___x_2530_;
v_a_2504_ = v_a_2543_;
goto v___jp_2501_;
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v___f_2459_);
lean_dec(v_a_2457_);
lean_dec(v___x_2417_);
v_a_2544_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2512_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2512_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v___x_2417_);
v_a_2579_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2432_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2432_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_dec(v___x_2417_);
v___x_2587_ = lean_box(0);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2587_);
v___x_2589_ = v___x_2428_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v___x_2417_);
v_a_2592_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2425_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2425_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2609_, size_t v_i_2610_, size_t v_stop_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_usize_dec_eq(v_i_2610_, v_stop_2611_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_array_uget_borrowed(v_as_2609_, v_i_2610_);
lean_inc_n(v___x_2621_, 2);
v___f_2622_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2622_, 0, v___x_2621_);
v___x_2623_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2621_, v___f_2622_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; size_t v___x_2625_; size_t v___x_2626_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = ((size_t)1ULL);
v___x_2626_ = lean_usize_add(v_i_2610_, v___x_2625_);
v_i_2610_ = v___x_2626_;
v_b_2612_ = v_a_2624_;
goto _start;
}
else
{
return v___x_2623_;
}
}
else
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_b_2612_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2629_, lean_object* v_i_2630_, lean_object* v_stop_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
size_t v_i_boxed_2640_; size_t v_stop_boxed_2641_; lean_object* v_res_2642_; 
v_i_boxed_2640_ = lean_unbox_usize(v_i_2630_);
lean_dec(v_i_2630_);
v_stop_boxed_2641_ = lean_unbox_usize(v_stop_2631_);
lean_dec(v_stop_2631_);
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2629_, v_i_boxed_2640_, v_stop_boxed_2641_, v_b_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v_as_2629_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2643_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2666_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2666_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2666_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_array_get_size(v_a_2652_);
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_nat_dec_lt(v___x_2656_, v___x_2657_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2661_; 
lean_dec(v_a_2652_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2658_);
v___x_2661_ = v___x_2654_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2658_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
else
{
size_t v___x_2663_; size_t v___x_2664_; lean_object* v___x_2665_; 
lean_del_object(v___x_2654_);
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = lean_usize_of_nat(v___x_2657_);
v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2652_, v___x_2663_, v___x_2664_, v___x_2658_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2652_);
return v___x_2665_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_a_2667_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2651_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2651_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2684_, v___y_2688_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v_mvarId_2693_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v_mvarId_2702_, lean_object* v_val_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2702_, v_val_2703_, v___y_2707_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v_mvarId_2712_, lean_object* v_val_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2712_, v_val_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object* v_00_u03b1_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_2723_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(v_00_u03b1_2732_, v_x_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2741_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
uint8_t v___x_2745_; 
v___x_2745_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2743_, v_x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_){
_start:
{
uint8_t v_res_2749_; lean_object* v_r_2750_; 
v_res_2749_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2746_, v_x_2747_, v_x_2748_);
lean_dec(v_x_2748_);
lean_dec_ref(v_x_2747_);
v_r_2750_ = lean_box(v_res_2749_);
return v_r_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object* v_00_u03b2_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_x_2752_, v_x_2753_, v_x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object* v_oldTraces_2756_, lean_object* v_data_2757_, lean_object* v_ref_2758_, lean_object* v_msg_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2756_, v_data_2757_, v_ref_2758_, v_msg_2759_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object* v_oldTraces_2768_, lean_object* v_data_2769_, lean_object* v_ref_2770_, lean_object* v_msg_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_oldTraces_2768_, v_data_2769_, v_ref_2770_, v_msg_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2779_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2780_, lean_object* v_x_2781_, size_t v_x_2782_, lean_object* v_x_2783_){
_start:
{
uint8_t v___x_2784_; 
v___x_2784_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2781_, v_x_2782_, v_x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
size_t v_x_18199__boxed_2789_; uint8_t v_res_2790_; lean_object* v_r_2791_; 
v_x_18199__boxed_2789_ = lean_unbox_usize(v_x_2787_);
lean_dec(v_x_2787_);
v_res_2790_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2785_, v_x_2786_, v_x_18199__boxed_2789_, v_x_2788_);
lean_dec(v_x_2788_);
lean_dec_ref(v_x_2786_);
v_r_2791_ = lean_box(v_res_2790_);
return v_r_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2792_, lean_object* v_x_2793_, size_t v_x_2794_, size_t v_x_2795_, lean_object* v_x_2796_, lean_object* v_x_2797_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2793_, v_x_2794_, v_x_2795_, v_x_2796_, v_x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
size_t v_x_18210__boxed_2805_; size_t v_x_18211__boxed_2806_; lean_object* v_res_2807_; 
v_x_18210__boxed_2805_ = lean_unbox_usize(v_x_2801_);
lean_dec(v_x_2801_);
v_x_18211__boxed_2806_ = lean_unbox_usize(v_x_2802_);
lean_dec(v_x_2802_);
v_res_2807_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(v_00_u03b2_2799_, v_x_2800_, v_x_18210__boxed_2805_, v_x_18211__boxed_2806_, v_x_2803_, v_x_2804_);
return v_res_2807_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2808_, lean_object* v_keys_2809_, lean_object* v_vals_2810_, lean_object* v_heq_2811_, lean_object* v_i_2812_, lean_object* v_k_2813_){
_start:
{
uint8_t v___x_2814_; 
v___x_2814_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2809_, v_i_2812_, v_k_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2815_, lean_object* v_keys_2816_, lean_object* v_vals_2817_, lean_object* v_heq_2818_, lean_object* v_i_2819_, lean_object* v_k_2820_){
_start:
{
uint8_t v_res_2821_; lean_object* v_r_2822_; 
v_res_2821_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2815_, v_keys_2816_, v_vals_2817_, v_heq_2818_, v_i_2819_, v_k_2820_);
lean_dec(v_k_2820_);
lean_dec_ref(v_vals_2817_);
lean_dec_ref(v_keys_2816_);
v_r_2822_ = lean_box(v_res_2821_);
return v_r_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_2823_, lean_object* v_n_2824_, lean_object* v_k_2825_, lean_object* v_v_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v_n_2824_, v_k_2825_, v_v_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b2_2828_, size_t v_depth_2829_, lean_object* v_keys_2830_, lean_object* v_vals_2831_, lean_object* v_heq_2832_, lean_object* v_i_2833_, lean_object* v_entries_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2829_, v_keys_2830_, v_vals_2831_, v_i_2833_, v_entries_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b2_2836_, lean_object* v_depth_2837_, lean_object* v_keys_2838_, lean_object* v_vals_2839_, lean_object* v_heq_2840_, lean_object* v_i_2841_, lean_object* v_entries_2842_){
_start:
{
size_t v_depth_boxed_2843_; lean_object* v_res_2844_; 
v_depth_boxed_2843_ = lean_unbox_usize(v_depth_2837_);
lean_dec(v_depth_2837_);
v_res_2844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(v_00_u03b2_2836_, v_depth_boxed_2843_, v_keys_2838_, v_vals_2839_, v_heq_2840_, v_i_2841_, v_entries_2842_);
lean_dec_ref(v_vals_2839_);
lean_dec_ref(v_keys_2838_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_, lean_object* v_x_2848_, lean_object* v_x_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_x_2846_, v_x_2847_, v_x_2848_, v_x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2851_, lean_object* v___y_2852_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Expr_hasMVar(v_e_2851_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_e_2851_);
return v___x_2855_;
}
else
{
lean_object* v___x_2856_; lean_object* v_mctx_2857_; lean_object* v___x_2858_; lean_object* v_fst_2859_; lean_object* v_snd_2860_; lean_object* v___x_2861_; lean_object* v_cache_2862_; lean_object* v_zetaDeltaFVarIds_2863_; lean_object* v_postponed_2864_; lean_object* v_diag_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2874_; 
v___x_2856_ = lean_st_ref_get(v___y_2852_);
v_mctx_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc_ref(v_mctx_2857_);
lean_dec(v___x_2856_);
v___x_2858_ = l_Lean_instantiateMVarsCore(v_mctx_2857_, v_e_2851_);
v_fst_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_fst_2859_);
v_snd_2860_ = lean_ctor_get(v___x_2858_, 1);
lean_inc(v_snd_2860_);
lean_dec_ref(v___x_2858_);
v___x_2861_ = lean_st_ref_take(v___y_2852_);
v_cache_2862_ = lean_ctor_get(v___x_2861_, 1);
v_zetaDeltaFVarIds_2863_ = lean_ctor_get(v___x_2861_, 2);
v_postponed_2864_ = lean_ctor_get(v___x_2861_, 3);
v_diag_2865_ = lean_ctor_get(v___x_2861_, 4);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2874_ == 0)
{
lean_object* v_unused_2875_; 
v_unused_2875_ = lean_ctor_get(v___x_2861_, 0);
lean_dec(v_unused_2875_);
v___x_2867_ = v___x_2861_;
v_isShared_2868_ = v_isSharedCheck_2874_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_diag_2865_);
lean_inc(v_postponed_2864_);
lean_inc(v_zetaDeltaFVarIds_2863_);
lean_inc(v_cache_2862_);
lean_dec(v___x_2861_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2874_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v_snd_2860_);
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_snd_2860_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_cache_2862_);
lean_ctor_set(v_reuseFailAlloc_2873_, 2, v_zetaDeltaFVarIds_2863_);
lean_ctor_set(v_reuseFailAlloc_2873_, 3, v_postponed_2864_);
lean_ctor_set(v_reuseFailAlloc_2873_, 4, v_diag_2865_);
v___x_2870_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_st_ref_put(v___y_2852_, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_fst_2859_);
return v___x_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2876_, v___y_2877_);
lean_dec(v___y_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2880_, v___y_2884_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2897_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_21097__overap_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_21097__overap_2908_ = lean_panic_fn_borrowed(v___x_2907_, v_msg_2899_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
lean_inc(v___y_2903_);
lean_inc_ref(v___y_2902_);
lean_inc(v___y_2901_);
lean_inc_ref(v___y_2900_);
v___x_2909_ = lean_apply_7(v___x_21097__overap_2908_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, lean_box(0));
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_a_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_a_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_a_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_2937_, lean_object* v_a_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_a_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_2947_, v_a_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___lam__0(lean_object* v_k_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v_b_2960_, lean_object* v_c_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; 
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2962_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
v___x_2967_ = lean_apply_9(v_k_2957_, v_b_2960_, v_c_2961_, v___y_2958_, v___y_2959_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, lean_box(0));
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___lam__0___boxed(lean_object* v_k_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v_b_2971_, lean_object* v_c_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___lam__0(v_k_2968_, v___y_2969_, v___y_2970_, v_b_2971_, v_c_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg(lean_object* v_type_2979_, lean_object* v_k_2980_, uint8_t v_cleanupAnnotations_2981_, uint8_t v_whnfType_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___f_2990_; lean_object* v___x_2991_; 
lean_inc(v___y_2984_);
lean_inc_ref(v___y_2983_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2990_, 0, v_k_2980_);
lean_closure_set(v___f_2990_, 1, v___y_2983_);
lean_closure_set(v___f_2990_, 2, v___y_2984_);
v___x_2991_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2979_, v___f_2990_, v_cleanupAnnotations_2981_, v_whnfType_2982_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_2991_) == 0)
{
return v___x_2991_;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg___boxed(lean_object* v_type_3000_, lean_object* v_k_3001_, lean_object* v_cleanupAnnotations_3002_, lean_object* v_whnfType_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3011_; uint8_t v_whnfType_boxed_3012_; lean_object* v_res_3013_; 
v_cleanupAnnotations_boxed_3011_ = lean_unbox(v_cleanupAnnotations_3002_);
v_whnfType_boxed_3012_ = lean_unbox(v_whnfType_3003_);
v_res_3013_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg(v_type_3000_, v_k_3001_, v_cleanupAnnotations_boxed_3011_, v_whnfType_boxed_3012_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9(lean_object* v_00_u03b1_3014_, lean_object* v_type_3015_, lean_object* v_k_3016_, uint8_t v_cleanupAnnotations_3017_, uint8_t v_whnfType_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg(v_type_3015_, v_k_3016_, v_cleanupAnnotations_3017_, v_whnfType_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___boxed(lean_object* v_00_u03b1_3027_, lean_object* v_type_3028_, lean_object* v_k_3029_, lean_object* v_cleanupAnnotations_3030_, lean_object* v_whnfType_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3039_; uint8_t v_whnfType_boxed_3040_; lean_object* v_res_3041_; 
v_cleanupAnnotations_boxed_3039_ = lean_unbox(v_cleanupAnnotations_3030_);
v_whnfType_boxed_3040_ = lean_unbox(v_whnfType_3031_);
v_res_3041_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9(v_00_u03b1_3027_, v_type_3028_, v_k_3029_, v_cleanupAnnotations_boxed_3039_, v_whnfType_boxed_3040_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
return v_res_3041_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3044_ = l_Lean_stringToMessageData(v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v_x_3055_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v___x_3064_, lean_object* v_fst_3065_, lean_object* v_____r_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = l_Lean_mkAppN(v___x_3064_, v_fst_3065_);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v___x_3076_, lean_object* v_fst_3077_, lean_object* v_____r_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3076_, v_fst_3077_, v_____r_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec_ref(v_fst_3077_);
return v_res_3086_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0));
v___x_3089_ = l_Lean_stringToMessageData(v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v_ctorName_3090_, uint8_t v___x_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3100_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1);
v___x_3101_ = l_Lean_MessageData_ofConstName(v_ctorName_3090_, v___x_3091_);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v_ctorName_3106_, lean_object* v___x_3107_, lean_object* v_x_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
uint8_t v___x_26008__boxed_3116_; lean_object* v_res_3117_; 
v___x_26008__boxed_3116_ = lean_unbox(v___x_3107_);
v_res_3117_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3106_, v___x_26008__boxed_3116_, v_x_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec_ref(v_x_3108_);
return v_res_3117_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___redArg(lean_object* v_k_3118_, lean_object* v_t_3119_){
_start:
{
if (lean_obj_tag(v_t_3119_) == 0)
{
lean_object* v_k_3120_; lean_object* v_l_3121_; lean_object* v_r_3122_; uint8_t v___x_3123_; 
v_k_3120_ = lean_ctor_get(v_t_3119_, 1);
v_l_3121_ = lean_ctor_get(v_t_3119_, 3);
v_r_3122_ = lean_ctor_get(v_t_3119_, 4);
v___x_3123_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3118_, v_k_3120_);
switch(v___x_3123_)
{
case 0:
{
v_t_3119_ = v_l_3121_;
goto _start;
}
case 1:
{
uint8_t v___x_3125_; 
v___x_3125_ = 1;
return v___x_3125_;
}
default: 
{
v_t_3119_ = v_r_3122_;
goto _start;
}
}
}
else
{
uint8_t v___x_3127_; 
v___x_3127_ = 0;
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___redArg___boxed(lean_object* v_k_3128_, lean_object* v_t_3129_){
_start:
{
uint8_t v_res_3130_; lean_object* v_r_3131_; 
v_res_3130_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___redArg(v_k_3128_, v_t_3129_);
lean_dec(v_t_3129_);
lean_dec(v_k_3128_);
v_r_3131_ = lean_box(v_res_3130_);
return v_r_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v___x_3132_, lean_object* v_as_3133_, size_t v_i_3134_, size_t v_stop_3135_, lean_object* v_b_3136_){
_start:
{
lean_object* v___y_3138_; uint8_t v___x_3142_; 
v___x_3142_ = lean_usize_dec_eq(v_i_3134_, v_stop_3135_);
if (v___x_3142_ == 0)
{
lean_object* v_fvarSet_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v_fvarSet_3143_ = lean_ctor_get(v___x_3132_, 1);
v___x_3144_ = lean_array_uget_borrowed(v_as_3133_, v_i_3134_);
v___x_3145_ = l_Lean_Expr_fvarId_x21(v___x_3144_);
v___x_3146_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___redArg(v___x_3145_, v_fvarSet_3143_);
lean_dec(v___x_3145_);
if (v___x_3146_ == 0)
{
v___y_3138_ = v_b_3136_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3147_; 
lean_inc(v___x_3144_);
v___x_3147_ = lean_array_push(v_b_3136_, v___x_3144_);
v___y_3138_ = v___x_3147_;
goto v___jp_3137_;
}
}
else
{
return v_b_3136_;
}
v___jp_3137_:
{
size_t v___x_3139_; size_t v___x_3140_; 
v___x_3139_ = ((size_t)1ULL);
v___x_3140_ = lean_usize_add(v_i_3134_, v___x_3139_);
v_i_3134_ = v___x_3140_;
v_b_3136_ = v___y_3138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v___x_3148_, lean_object* v_as_3149_, lean_object* v_i_3150_, lean_object* v_stop_3151_, lean_object* v_b_3152_){
_start:
{
size_t v_i_boxed_3153_; size_t v_stop_boxed_3154_; lean_object* v_res_3155_; 
v_i_boxed_3153_ = lean_unbox_usize(v_i_3150_);
lean_dec(v_i_3150_);
v_stop_boxed_3154_ = lean_unbox_usize(v_stop_3151_);
lean_dec(v_stop_3151_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3148_, v_as_3149_, v_i_boxed_3153_, v_stop_boxed_3154_, v_b_3152_);
lean_dec_ref(v_as_3149_);
lean_dec_ref(v___x_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
if (lean_obj_tag(v_a_3156_) == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = l_List_reverse___redArg(v_a_3157_);
return v___x_3158_;
}
else
{
lean_object* v_head_3159_; lean_object* v_tail_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3169_; 
v_head_3159_ = lean_ctor_get(v_a_3156_, 0);
v_tail_3160_ = lean_ctor_get(v_a_3156_, 1);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_a_3156_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3162_ = v_a_3156_;
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_tail_3160_);
lean_inc(v_head_3159_);
lean_dec(v_a_3156_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = l_Lean_MessageData_ofExpr(v_head_3159_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v_a_3157_);
lean_ctor_set(v___x_3162_, 0, v___x_3164_);
v___x_3166_ = v___x_3162_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_a_3157_);
v___x_3166_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
v_a_3156_ = v_tail_3160_;
v_a_3157_ = v___x_3166_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6_spec__6(lean_object* v_e_3170_){
_start:
{
if (lean_obj_tag(v_e_3170_) == 0)
{
uint8_t v___x_3171_; 
v___x_3171_ = 2;
return v___x_3171_;
}
else
{
lean_object* v_a_3172_; uint8_t v___x_3173_; 
v_a_3172_ = lean_ctor_get(v_e_3170_, 0);
v___x_3173_ = l_Lean_Expr_hasSyntheticSorry(v_a_3172_);
if (v___x_3173_ == 0)
{
uint8_t v___x_3174_; 
v___x_3174_ = 0;
return v___x_3174_;
}
else
{
uint8_t v___x_3175_; 
v___x_3175_ = 1;
return v___x_3175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6_spec__6___boxed(lean_object* v_e_3176_){
_start:
{
uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_res_3177_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6_spec__6(v_e_3176_);
lean_dec_ref(v_e_3176_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_cls_3179_, uint8_t v_collapsed_3180_, lean_object* v_tag_3181_, lean_object* v_opts_3182_, uint8_t v_clsEnabled_3183_, lean_object* v_oldTraces_3184_, lean_object* v_msg_3185_, lean_object* v_resStartStop_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_fst_3194_; lean_object* v_snd_3195_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v_data_3199_; lean_object* v_fst_3210_; lean_object* v_snd_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___y_3215_; lean_object* v_a_3216_; uint8_t v___y_3231_; double v___y_3263_; 
v_fst_3194_ = lean_ctor_get(v_resStartStop_3186_, 0);
lean_inc(v_fst_3194_);
v_snd_3195_ = lean_ctor_get(v_resStartStop_3186_, 1);
lean_inc(v_snd_3195_);
lean_dec_ref(v_resStartStop_3186_);
v_fst_3210_ = lean_ctor_get(v_snd_3195_, 0);
lean_inc(v_fst_3210_);
v_snd_3211_ = lean_ctor_get(v_snd_3195_, 1);
lean_inc(v_snd_3211_);
lean_dec(v_snd_3195_);
v___x_3212_ = l_Lean_trace_profiler;
v___x_3213_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3182_, v___x_3212_);
if (v___x_3213_ == 0)
{
v___y_3231_ = v___x_3213_;
goto v___jp_3230_;
}
else
{
lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3269_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3182_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; double v___x_3272_; double v___x_3273_; double v___x_3274_; 
v___x_3270_ = l_Lean_trace_profiler_threshold;
v___x_3271_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3182_, v___x_3270_);
v___x_3272_ = lean_float_of_nat(v___x_3271_);
v___x_3273_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_3274_ = lean_float_div(v___x_3272_, v___x_3273_);
v___y_3263_ = v___x_3274_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; double v___x_3277_; 
v___x_3275_ = l_Lean_trace_profiler_threshold;
v___x_3276_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3182_, v___x_3275_);
v___x_3277_ = lean_float_of_nat(v___x_3276_);
v___y_3263_ = v___x_3277_;
goto v___jp_3262_;
}
}
v___jp_3196_:
{
lean_object* v___x_3200_; 
lean_inc(v___y_3197_);
v___x_3200_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_3184_, v_data_3199_, v___y_3197_, v___y_3198_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v___x_3201_; 
lean_dec_ref_known(v___x_3200_, 1);
v___x_3201_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3194_);
return v___x_3201_;
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_fst_3194_);
v_a_3202_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3200_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3200_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
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
v___jp_3214_:
{
uint8_t v_result_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; double v___x_3220_; lean_object* v_data_3221_; 
v_result_3217_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6_spec__6(v_fst_3194_);
v___x_3218_ = lean_box(v_result_3217_);
v___x_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
v___x_3220_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3181_);
lean_inc_ref(v___x_3219_);
lean_inc(v_cls_3179_);
v_data_3221_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3221_, 0, v_cls_3179_);
lean_ctor_set(v_data_3221_, 1, v___x_3219_);
lean_ctor_set(v_data_3221_, 2, v_tag_3181_);
lean_ctor_set_float(v_data_3221_, sizeof(void*)*3, v___x_3220_);
lean_ctor_set_float(v_data_3221_, sizeof(void*)*3 + 8, v___x_3220_);
lean_ctor_set_uint8(v_data_3221_, sizeof(void*)*3 + 16, v_collapsed_3180_);
if (v___x_3213_ == 0)
{
lean_dec_ref_known(v___x_3219_, 1);
lean_dec(v_snd_3211_);
lean_dec(v_fst_3210_);
lean_dec_ref(v_tag_3181_);
lean_dec(v_cls_3179_);
v___y_3197_ = v___y_3215_;
v___y_3198_ = v_a_3216_;
v_data_3199_ = v_data_3221_;
goto v___jp_3196_;
}
else
{
lean_object* v_data_3222_; double v___x_3223_; double v___x_3224_; 
lean_dec_ref_known(v_data_3221_, 3);
v_data_3222_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3222_, 0, v_cls_3179_);
lean_ctor_set(v_data_3222_, 1, v___x_3219_);
lean_ctor_set(v_data_3222_, 2, v_tag_3181_);
v___x_3223_ = lean_unbox_float(v_fst_3210_);
lean_dec(v_fst_3210_);
lean_ctor_set_float(v_data_3222_, sizeof(void*)*3, v___x_3223_);
v___x_3224_ = lean_unbox_float(v_snd_3211_);
lean_dec(v_snd_3211_);
lean_ctor_set_float(v_data_3222_, sizeof(void*)*3 + 8, v___x_3224_);
lean_ctor_set_uint8(v_data_3222_, sizeof(void*)*3 + 16, v_collapsed_3180_);
v___y_3197_ = v___y_3215_;
v___y_3198_ = v_a_3216_;
v_data_3199_ = v_data_3222_;
goto v___jp_3196_;
}
}
v___jp_3225_:
{
lean_object* v_ref_3226_; lean_object* v___x_3227_; 
v_ref_3226_ = lean_ctor_get(v___y_3191_, 2);
lean_inc(v___y_3192_);
lean_inc_ref(v___y_3191_);
lean_inc(v___y_3190_);
lean_inc_ref(v___y_3189_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v_fst_3194_);
v___x_3227_ = lean_apply_8(v_msg_3185_, v_fst_3194_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, lean_box(0));
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
v___y_3215_ = v_ref_3226_;
v_a_3216_ = v_a_3228_;
goto v___jp_3214_;
}
else
{
lean_object* v___x_3229_; 
lean_dec_ref_known(v___x_3227_, 1);
v___x_3229_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_3215_ = v_ref_3226_;
v_a_3216_ = v___x_3229_;
goto v___jp_3214_;
}
}
v___jp_3230_:
{
if (v_clsEnabled_3183_ == 0)
{
if (v___y_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v_traceState_3233_; lean_object* v_env_3234_; lean_object* v_nextMacroScope_3235_; lean_object* v_ngen_3236_; lean_object* v_auxDeclNGen_3237_; lean_object* v_cache_3238_; lean_object* v_recordedDeps_3239_; lean_object* v_messages_3240_; lean_object* v_infoState_3241_; lean_object* v_snapshotTasks_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3261_; 
lean_dec(v_snd_3211_);
lean_dec(v_fst_3210_);
lean_dec_ref(v_msg_3185_);
lean_dec_ref(v_tag_3181_);
lean_dec(v_cls_3179_);
v___x_3232_ = lean_st_ref_take(v___y_3192_);
v_traceState_3233_ = lean_ctor_get(v___x_3232_, 4);
v_env_3234_ = lean_ctor_get(v___x_3232_, 0);
v_nextMacroScope_3235_ = lean_ctor_get(v___x_3232_, 1);
v_ngen_3236_ = lean_ctor_get(v___x_3232_, 2);
v_auxDeclNGen_3237_ = lean_ctor_get(v___x_3232_, 3);
v_cache_3238_ = lean_ctor_get(v___x_3232_, 5);
v_recordedDeps_3239_ = lean_ctor_get(v___x_3232_, 6);
v_messages_3240_ = lean_ctor_get(v___x_3232_, 7);
v_infoState_3241_ = lean_ctor_get(v___x_3232_, 8);
v_snapshotTasks_3242_ = lean_ctor_get(v___x_3232_, 9);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3244_ = v___x_3232_;
v_isShared_3245_ = v_isSharedCheck_3261_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_snapshotTasks_3242_);
lean_inc(v_infoState_3241_);
lean_inc(v_messages_3240_);
lean_inc(v_recordedDeps_3239_);
lean_inc(v_cache_3238_);
lean_inc(v_traceState_3233_);
lean_inc(v_auxDeclNGen_3237_);
lean_inc(v_ngen_3236_);
lean_inc(v_nextMacroScope_3235_);
lean_inc(v_env_3234_);
lean_dec(v___x_3232_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3261_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
uint64_t v_tid_3246_; lean_object* v_traces_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3260_; 
v_tid_3246_ = lean_ctor_get_uint64(v_traceState_3233_, sizeof(void*)*1);
v_traces_3247_ = lean_ctor_get(v_traceState_3233_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_traceState_3233_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3249_ = v_traceState_3233_;
v_isShared_3250_ = v_isSharedCheck_3260_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_traces_3247_);
lean_dec(v_traceState_3233_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3260_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3251_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3184_, v_traces_3247_);
lean_dec_ref(v_traces_3247_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3251_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3251_);
lean_ctor_set_uint64(v_reuseFailAlloc_3259_, sizeof(void*)*1, v_tid_3246_);
v___x_3253_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3255_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 4, v___x_3253_);
v___x_3255_ = v___x_3244_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_env_3234_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_nextMacroScope_3235_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_ngen_3236_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v_auxDeclNGen_3237_);
lean_ctor_set(v_reuseFailAlloc_3258_, 4, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3258_, 5, v_cache_3238_);
lean_ctor_set(v_reuseFailAlloc_3258_, 6, v_recordedDeps_3239_);
lean_ctor_set(v_reuseFailAlloc_3258_, 7, v_messages_3240_);
lean_ctor_set(v_reuseFailAlloc_3258_, 8, v_infoState_3241_);
lean_ctor_set(v_reuseFailAlloc_3258_, 9, v_snapshotTasks_3242_);
v___x_3255_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = lean_st_ref_put(v___y_3192_, v___x_3255_);
v___x_3257_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3194_);
return v___x_3257_;
}
}
}
}
}
else
{
goto v___jp_3225_;
}
}
else
{
goto v___jp_3225_;
}
}
v___jp_3262_:
{
double v___x_3264_; double v___x_3265_; double v___x_3266_; uint8_t v___x_3267_; 
v___x_3264_ = lean_unbox_float(v_snd_3211_);
v___x_3265_ = lean_unbox_float(v_fst_3210_);
v___x_3266_ = lean_float_sub(v___x_3264_, v___x_3265_);
v___x_3267_ = lean_float_decLt(v___y_3263_, v___x_3266_);
v___y_3231_ = v___x_3267_;
goto v___jp_3230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_cls_3278_, lean_object* v_collapsed_3279_, lean_object* v_tag_3280_, lean_object* v_opts_3281_, lean_object* v_clsEnabled_3282_, lean_object* v_oldTraces_3283_, lean_object* v_msg_3284_, lean_object* v_resStartStop_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
uint8_t v_collapsed_boxed_3293_; uint8_t v_clsEnabled_boxed_3294_; lean_object* v_res_3295_; 
v_collapsed_boxed_3293_ = lean_unbox(v_collapsed_3279_);
v_clsEnabled_boxed_3294_ = lean_unbox(v_clsEnabled_3282_);
v_res_3295_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_cls_3278_, v_collapsed_boxed_3293_, v_tag_3280_, v_opts_3281_, v_clsEnabled_boxed_3294_, v_oldTraces_3283_, v_msg_3284_, v_resStartStop_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec_ref(v_opts_3281_);
return v_res_3295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3299_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3300_ = lean_unsigned_to_nat(6u);
v___x_3301_ = lean_unsigned_to_nat(108u);
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3303_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3304_ = l_mkPanicMessageWithDecl(v___x_3303_, v___x_3302_, v___x_3301_, v___x_3300_, v___x_3299_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11));
v___x_3318_ = l_Lean_stringToMessageData(v___x_3317_);
return v___x_3318_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13));
v___x_3321_ = l_Lean_stringToMessageData(v___x_3320_);
return v___x_3321_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15));
v___x_3324_ = l_Lean_stringToMessageData(v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3332_, lean_object* v_us_3333_, lean_object* v_xs_3334_, lean_object* v___x_3335_, lean_object* v_ctorName_3336_, lean_object* v___x_3337_, lean_object* v___f_3338_, lean_object* v_insts_3339_, lean_object* v_localInst2Index_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; lean_object* v_type_3349_; lean_object* v___y_3351_; uint8_t v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v_val_3480_; lean_object* v___y_3507_; lean_object* v___y_3518_; lean_object* v___x_3528_; lean_object* v_env_3529_; uint8_t v___x_3530_; uint8_t v___x_3531_; 
lean_inc(v_us_3333_);
lean_inc(v_inductiveTypeName_3332_);
v___x_3348_ = l_Lean_Expr_const___override(v_inductiveTypeName_3332_, v_us_3333_);
v_type_3349_ = l_Lean_mkAppN(v___x_3348_, v_xs_3334_);
v___x_3528_ = lean_st_ref_get(v___y_3346_);
v_env_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc_ref(v_env_3529_);
lean_dec(v___x_3528_);
v___x_3530_ = l_Lean_isStructure(v_env_3529_, v_inductiveTypeName_3332_);
v___x_3531_ = 1;
if (v___x_3530_ == 0)
{
lean_object* v_toCold_3532_; lean_object* v_options_3533_; lean_object* v_inheritedTraceOptions_3534_; uint8_t v_hasTrace_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec_ref(v___f_3338_);
v_toCold_3532_ = lean_ctor_get(v___y_3345_, 0);
v_options_3533_ = lean_ctor_get(v_toCold_3532_, 2);
v_inheritedTraceOptions_3534_ = lean_ctor_get(v_toCold_3532_, 11);
v_hasTrace_3535_ = lean_ctor_get_uint8(v_options_3533_, sizeof(void*)*1);
lean_inc(v_ctorName_3336_);
v___x_3536_ = l_Lean_Expr_const___override(v_ctorName_3336_, v_us_3333_);
v___x_3537_ = l_Lean_mkAppN(v___x_3536_, v___x_3337_);
if (v_hasTrace_3535_ == 0)
{
lean_object* v___x_3538_; 
lean_dec(v_ctorName_3336_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3537_);
v___x_3538_ = lean_infer_type(v___x_3537_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; lean_object* v___x_3542_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3538_, 1);
v___x_3540_ = lean_box(0);
v___x_3541_ = 0;
v___x_3542_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3539_, v___x_3540_, v___x_3541_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v_snd_3544_; lean_object* v_fst_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3588_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v_snd_3544_ = lean_ctor_get(v_a_3543_, 1);
v_fst_3545_ = lean_ctor_get(v_a_3543_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_a_3543_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3547_ = v_a_3543_;
v_isShared_3548_ = v_isSharedCheck_3588_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_snd_3544_);
lean_inc(v_fst_3545_);
lean_dec(v_a_3543_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3588_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v_snd_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3586_; 
v_snd_3549_ = lean_ctor_get(v_snd_3544_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_snd_3544_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v_snd_3544_, 0);
lean_dec(v_unused_3587_);
v___x_3551_ = v_snd_3544_;
v_isShared_3552_ = v_isSharedCheck_3586_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_snd_3549_);
lean_dec(v_snd_3544_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3586_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; 
lean_inc(v_snd_3549_);
lean_inc_ref(v_type_3349_);
v___x_3553_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3549_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; uint8_t v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = lean_unbox(v_a_3554_);
lean_dec(v_a_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
lean_dec(v_fst_3545_);
lean_dec_ref(v___x_3537_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v___x_3556_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14);
v___x_3557_ = l_Lean_indentExpr(v_type_3349_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set_tag(v___x_3551_, 7);
lean_ctor_set(v___x_3551_, 1, v___x_3557_);
lean_ctor_set(v___x_3551_, 0, v___x_3556_);
v___x_3559_ = v___x_3551_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3560_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
if (v_isShared_3548_ == 0)
{
lean_ctor_set_tag(v___x_3547_, 7);
lean_ctor_set(v___x_3547_, 1, v___x_3560_);
lean_ctor_set(v___x_3547_, 0, v___x_3559_);
v___x_3562_ = v___x_3547_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
v___x_3563_ = l_Lean_indentExpr(v_snd_3549_);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3564_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3565_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3565_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_del_object(v___x_3551_);
lean_dec(v_snd_3549_);
lean_del_object(v___x_3547_);
v___x_3576_ = lean_box(0);
v___x_3577_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3537_, v_fst_3545_, v___x_3576_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3545_);
v___y_3518_ = v___x_3577_;
goto v___jp_3517_;
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_del_object(v___x_3551_);
lean_dec(v_snd_3549_);
lean_del_object(v___x_3547_);
lean_dec(v_fst_3545_);
lean_dec_ref(v___x_3537_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3578_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3553_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3553_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v___x_3537_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3589_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3542_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3542_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v___x_3537_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3597_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3538_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3538_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
else
{
lean_object* v___x_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v_a_3614_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v_a_3629_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v_a_3646_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v_a_3658_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; 
v___x_3605_ = lean_box(v___x_3530_);
v___f_3606_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3606_, 0, v_ctorName_3336_);
lean_closure_set(v___f_3606_, 1, v___x_3605_);
v___x_3607_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3608_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3609_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3534_, v_options_3533_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3757_ = l_Lean_trace_profiler;
v___x_3758_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3533_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
lean_dec_ref(v___f_3606_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3537_);
v___x_3759_ = lean_infer_type(v___x_3537_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = lean_box(0);
v___x_3762_ = 0;
v___x_3763_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3760_, v___x_3761_, v___x_3762_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v_snd_3765_; lean_object* v_fst_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3809_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v_snd_3765_ = lean_ctor_get(v_a_3764_, 1);
v_fst_3766_ = lean_ctor_get(v_a_3764_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_a_3764_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3768_ = v_a_3764_;
v_isShared_3769_ = v_isSharedCheck_3809_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_snd_3765_);
lean_inc(v_fst_3766_);
lean_dec(v_a_3764_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3809_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v_snd_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3807_; 
v_snd_3770_ = lean_ctor_get(v_snd_3765_, 1);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_snd_3765_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; 
v_unused_3808_ = lean_ctor_get(v_snd_3765_, 0);
lean_dec(v_unused_3808_);
v___x_3772_ = v_snd_3765_;
v_isShared_3773_ = v_isSharedCheck_3807_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_snd_3770_);
lean_dec(v_snd_3765_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3807_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; 
lean_inc(v_snd_3770_);
lean_inc_ref(v_type_3349_);
v___x_3774_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3770_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; uint8_t v___x_3776_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v___x_3774_, 1);
v___x_3776_ = lean_unbox(v_a_3775_);
lean_dec(v_a_3775_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3780_; 
lean_dec(v_fst_3766_);
lean_dec_ref(v___x_3537_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v___x_3777_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14);
v___x_3778_ = l_Lean_indentExpr(v_type_3349_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 7);
lean_ctor_set(v___x_3772_, 1, v___x_3778_);
lean_ctor_set(v___x_3772_, 0, v___x_3777_);
v___x_3780_ = v___x_3772_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3781_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
if (v_isShared_3769_ == 0)
{
lean_ctor_set_tag(v___x_3768_, 7);
lean_ctor_set(v___x_3768_, 1, v___x_3781_);
lean_ctor_set(v___x_3768_, 0, v___x_3780_);
v___x_3783_ = v___x_3768_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
v___x_3784_ = l_Lean_indentExpr(v_snd_3770_);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3785_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_del_object(v___x_3772_);
lean_dec(v_snd_3770_);
lean_del_object(v___x_3768_);
v___x_3797_ = lean_box(0);
v___x_3798_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3537_, v_fst_3766_, v___x_3797_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3766_);
v___y_3518_ = v___x_3798_;
goto v___jp_3517_;
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_del_object(v___x_3772_);
lean_dec(v_snd_3770_);
lean_del_object(v___x_3768_);
lean_dec(v_fst_3766_);
lean_dec_ref(v___x_3537_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3799_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3774_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3774_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v___x_3537_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3810_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3763_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3763_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v___x_3537_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3818_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3759_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3759_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
goto v___jp_3672_;
}
}
else
{
goto v___jp_3672_;
}
v___jp_3611_:
{
lean_object* v___x_3615_; double v___x_3616_; double v___x_3617_; double v___x_3618_; double v___x_3619_; double v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3615_ = lean_io_mono_nanos_now();
v___x_3616_ = lean_float_of_nat(v___y_3613_);
v___x_3617_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3618_ = lean_float_div(v___x_3616_, v___x_3617_);
v___x_3619_ = lean_float_of_nat(v___x_3615_);
v___x_3620_ = lean_float_div(v___x_3619_, v___x_3617_);
v___x_3621_ = lean_box_float(v___x_3618_);
v___x_3622_ = lean_box_float(v___x_3620_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v_a_3614_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v___x_3607_, v___x_3531_, v___x_3608_, v_options_3533_, v___x_3610_, v___y_3612_, v___f_3606_, v___x_3624_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3518_ = v___x_3625_;
goto v___jp_3517_;
}
v___jp_3626_:
{
lean_object* v___x_3630_; 
v___x_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3630_, 0, v_a_3629_);
v___y_3612_ = v___y_3627_;
v___y_3613_ = v___y_3628_;
v_a_3614_ = v___x_3630_;
goto v___jp_3611_;
}
v___jp_3631_:
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___y_3634_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___y_3634_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___y_3634_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___y_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 1);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
v___y_3612_ = v___y_3632_;
v___y_3613_ = v___y_3633_;
v_a_3614_ = v___x_3640_;
goto v___jp_3611_;
}
}
}
v___jp_3643_:
{
lean_object* v___x_3647_; double v___x_3648_; double v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3647_ = lean_io_get_num_heartbeats();
v___x_3648_ = lean_float_of_nat(v___y_3644_);
v___x_3649_ = lean_float_of_nat(v___x_3647_);
v___x_3650_ = lean_box_float(v___x_3648_);
v___x_3651_ = lean_box_float(v___x_3649_);
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3650_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v_a_3646_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v___x_3607_, v___x_3531_, v___x_3608_, v_options_3533_, v___x_3610_, v___y_3645_, v___f_3606_, v___x_3653_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3518_ = v___x_3654_;
goto v___jp_3517_;
}
v___jp_3655_:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v_a_3658_);
v___y_3644_ = v___y_3656_;
v___y_3645_ = v___y_3657_;
v_a_3646_ = v___x_3659_;
goto v___jp_3643_;
}
v___jp_3660_:
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
v_a_3664_ = lean_ctor_get(v___y_3663_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___y_3663_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___y_3663_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___y_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 1);
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
v___y_3644_ = v___y_3661_;
v___y_3645_ = v___y_3662_;
v_a_3646_ = v___x_3669_;
goto v___jp_3643_;
}
}
}
v___jp_3672_:
{
lean_object* v___x_3673_; lean_object* v_a_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3673_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3346_);
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___x_3675_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3676_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3533_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = lean_io_mono_nanos_now();
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3537_);
v___x_3678_ = lean_infer_type(v___x_3537_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3680_ = lean_box(0);
v___x_3681_ = 0;
v___x_3682_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3679_, v___x_3680_, v___x_3681_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v_snd_3684_; lean_object* v_fst_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3714_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v_snd_3684_ = lean_ctor_get(v_a_3683_, 1);
v_fst_3685_ = lean_ctor_get(v_a_3683_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_a_3683_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3687_ = v_a_3683_;
v_isShared_3688_ = v_isSharedCheck_3714_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_snd_3684_);
lean_inc(v_fst_3685_);
lean_dec(v_a_3683_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3714_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v_snd_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3712_; 
v_snd_3689_ = lean_ctor_get(v_snd_3684_, 1);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_snd_3684_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; 
v_unused_3713_ = lean_ctor_get(v_snd_3684_, 0);
lean_dec(v_unused_3713_);
v___x_3691_ = v_snd_3684_;
v_isShared_3692_ = v_isSharedCheck_3712_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_snd_3689_);
lean_dec(v_snd_3684_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3712_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; 
lean_inc(v_snd_3689_);
lean_inc_ref(v_type_3349_);
v___x_3693_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3689_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; uint8_t v___x_3695_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v___x_3695_ = lean_unbox(v_a_3694_);
lean_dec(v_a_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
lean_dec(v_fst_3685_);
lean_dec_ref(v___x_3537_);
v___x_3696_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14);
lean_inc_ref(v_type_3349_);
v___x_3697_ = l_Lean_indentExpr(v_type_3349_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set_tag(v___x_3691_, 7);
lean_ctor_set(v___x_3691_, 1, v___x_3697_);
lean_ctor_set(v___x_3691_, 0, v___x_3696_);
v___x_3699_ = v___x_3691_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3700_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 7);
lean_ctor_set(v___x_3687_, 1, v___x_3700_);
lean_ctor_set(v___x_3687_, 0, v___x_3699_);
v___x_3702_ = v___x_3687_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v_a_3706_; 
v___x_3703_ = l_Lean_indentExpr(v_snd_3689_);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3704_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3705_);
v___y_3627_ = v_a_3674_;
v___y_3628_ = v___x_3677_;
v_a_3629_ = v_a_3706_;
goto v___jp_3626_;
}
}
}
else
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_del_object(v___x_3691_);
lean_dec(v_snd_3689_);
lean_del_object(v___x_3687_);
v___x_3709_ = lean_box(0);
v___x_3710_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3537_, v_fst_3685_, v___x_3709_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3685_);
v___y_3632_ = v_a_3674_;
v___y_3633_ = v___x_3677_;
v___y_3634_ = v___x_3710_;
goto v___jp_3631_;
}
}
else
{
lean_object* v_a_3711_; 
lean_del_object(v___x_3691_);
lean_dec(v_snd_3689_);
lean_del_object(v___x_3687_);
lean_dec(v_fst_3685_);
lean_dec_ref(v___x_3537_);
v_a_3711_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3693_, 1);
v___y_3627_ = v_a_3674_;
v___y_3628_ = v___x_3677_;
v_a_3629_ = v_a_3711_;
goto v___jp_3626_;
}
}
}
}
else
{
lean_object* v_a_3715_; 
lean_dec_ref(v___x_3537_);
v_a_3715_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3715_);
lean_dec_ref_known(v___x_3682_, 1);
v___y_3627_ = v_a_3674_;
v___y_3628_ = v___x_3677_;
v_a_3629_ = v_a_3715_;
goto v___jp_3626_;
}
}
else
{
lean_object* v_a_3716_; 
lean_dec_ref(v___x_3537_);
v_a_3716_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3678_, 1);
v___y_3627_ = v_a_3674_;
v___y_3628_ = v___x_3677_;
v_a_3629_ = v_a_3716_;
goto v___jp_3626_;
}
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3537_);
v___x_3718_ = lean_infer_type(v___x_3537_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v___x_3720_ = lean_box(0);
v___x_3721_ = 0;
v___x_3722_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3719_, v___x_3720_, v___x_3721_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v_snd_3724_; lean_object* v_fst_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3754_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v_snd_3724_ = lean_ctor_get(v_a_3723_, 1);
v_fst_3725_ = lean_ctor_get(v_a_3723_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_a_3723_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3727_ = v_a_3723_;
v_isShared_3728_ = v_isSharedCheck_3754_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_snd_3724_);
lean_inc(v_fst_3725_);
lean_dec(v_a_3723_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3754_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v_snd_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3752_; 
v_snd_3729_ = lean_ctor_get(v_snd_3724_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_snd_3724_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; 
v_unused_3753_ = lean_ctor_get(v_snd_3724_, 0);
lean_dec(v_unused_3753_);
v___x_3731_ = v_snd_3724_;
v_isShared_3732_ = v_isSharedCheck_3752_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_snd_3729_);
lean_dec(v_snd_3724_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3752_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; 
lean_inc(v_snd_3729_);
lean_inc_ref(v_type_3349_);
v___x_3733_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3729_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; uint8_t v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = lean_unbox(v_a_3734_);
lean_dec(v_a_3734_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
lean_dec(v_fst_3725_);
lean_dec_ref(v___x_3537_);
v___x_3736_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14);
lean_inc_ref(v_type_3349_);
v___x_3737_ = l_Lean_indentExpr(v_type_3349_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set_tag(v___x_3731_, 7);
lean_ctor_set(v___x_3731_, 1, v___x_3737_);
lean_ctor_set(v___x_3731_, 0, v___x_3736_);
v___x_3739_ = v___x_3731_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3740_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16);
if (v_isShared_3728_ == 0)
{
lean_ctor_set_tag(v___x_3727_, 7);
lean_ctor_set(v___x_3727_, 1, v___x_3740_);
lean_ctor_set(v___x_3727_, 0, v___x_3739_);
v___x_3742_ = v___x_3727_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v_a_3746_; 
v___x_3743_ = l_Lean_indentExpr(v_snd_3729_);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3744_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref(v___x_3745_);
v___y_3656_ = v___x_3717_;
v___y_3657_ = v_a_3674_;
v_a_3658_ = v_a_3746_;
goto v___jp_3655_;
}
}
}
else
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_del_object(v___x_3731_);
lean_dec(v_snd_3729_);
lean_del_object(v___x_3727_);
v___x_3749_ = lean_box(0);
v___x_3750_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3537_, v_fst_3725_, v___x_3749_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3725_);
v___y_3661_ = v___x_3717_;
v___y_3662_ = v_a_3674_;
v___y_3663_ = v___x_3750_;
goto v___jp_3660_;
}
}
else
{
lean_object* v_a_3751_; 
lean_del_object(v___x_3731_);
lean_dec(v_snd_3729_);
lean_del_object(v___x_3727_);
lean_dec(v_fst_3725_);
lean_dec_ref(v___x_3537_);
v_a_3751_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3733_, 1);
v___y_3656_ = v___x_3717_;
v___y_3657_ = v_a_3674_;
v_a_3658_ = v_a_3751_;
goto v___jp_3655_;
}
}
}
}
else
{
lean_object* v_a_3755_; 
lean_dec_ref(v___x_3537_);
v_a_3755_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3722_, 1);
v___y_3656_ = v___x_3717_;
v___y_3657_ = v_a_3674_;
v_a_3658_ = v_a_3755_;
goto v___jp_3655_;
}
}
else
{
lean_object* v_a_3756_; 
lean_dec_ref(v___x_3537_);
v_a_3756_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3718_, 1);
v___y_3656_ = v___x_3717_;
v___y_3657_ = v_a_3674_;
v_a_3658_ = v_a_3756_;
goto v___jp_3655_;
}
}
}
}
}
else
{
lean_object* v_toCold_3826_; lean_object* v_options_3827_; uint8_t v_hasTrace_3828_; 
lean_dec(v_ctorName_3336_);
lean_dec(v_us_3333_);
v_toCold_3826_ = lean_ctor_get(v___y_3345_, 0);
v_options_3827_ = lean_ctor_get(v_toCold_3826_, 2);
v_hasTrace_3828_ = lean_ctor_get_uint8(v_options_3827_, sizeof(void*)*1);
if (v_hasTrace_3828_ == 0)
{
lean_object* v_ref_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_dec_ref(v___f_3338_);
v_ref_3829_ = lean_ctor_get(v___y_3345_, 2);
v___x_3830_ = l_Lean_SourceInfo_fromRef(v_ref_3829_, v_hasTrace_3828_);
v___x_3831_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18));
v___x_3832_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
lean_inc(v___x_3830_);
v___x_3833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3830_);
lean_ctor_set(v___x_3833_, 1, v___x_3832_);
v___x_3834_ = l_Lean_Syntax_node1(v___x_3830_, v___x_3831_, v___x_3833_);
lean_inc_ref(v_type_3349_);
v___x_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3835_, 0, v_type_3349_);
v___x_3836_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3836_, 0, v___x_3834_);
lean_closure_set(v___x_3836_, 1, v___x_3835_);
v___x_3837_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3836_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3507_ = v___x_3837_;
goto v___jp_3506_;
}
else
{
lean_object* v_ref_3838_; lean_object* v_inheritedTraceOptions_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v_a_3847_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v_a_3862_; 
v_ref_3838_ = lean_ctor_get(v___y_3345_, 2);
v_inheritedTraceOptions_3839_ = lean_ctor_get(v_toCold_3826_, 11);
v___x_3840_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3841_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3842_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3843_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3839_, v_options_3827_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = l_Lean_trace_profiler;
v___x_3936_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3827_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec_ref(v___f_3338_);
v___x_3937_ = l_Lean_SourceInfo_fromRef(v_ref_3838_, v___x_3936_);
v___x_3938_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18));
v___x_3939_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
lean_inc(v___x_3937_);
v___x_3940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3937_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = l_Lean_Syntax_node1(v___x_3937_, v___x_3938_, v___x_3940_);
lean_inc_ref(v_type_3349_);
v___x_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3942_, 0, v_type_3349_);
v___x_3943_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3943_, 0, v___x_3941_);
lean_closure_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3943_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3507_ = v___x_3944_;
goto v___jp_3506_;
}
else
{
goto v___jp_3871_;
}
}
else
{
goto v___jp_3871_;
}
v___jp_3844_:
{
lean_object* v___x_3848_; double v___x_3849_; double v___x_3850_; double v___x_3851_; double v___x_3852_; double v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3848_ = lean_io_mono_nanos_now();
v___x_3849_ = lean_float_of_nat(v___y_3846_);
v___x_3850_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3851_ = lean_float_div(v___x_3849_, v___x_3850_);
v___x_3852_ = lean_float_of_nat(v___x_3848_);
v___x_3853_ = lean_float_div(v___x_3852_, v___x_3850_);
v___x_3854_ = lean_box_float(v___x_3851_);
v___x_3855_ = lean_box_float(v___x_3853_);
v___x_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3854_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v_a_3847_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
v___x_3858_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v___x_3840_, v___x_3531_, v___x_3841_, v_options_3827_, v___x_3843_, v___y_3845_, v___f_3338_, v___x_3857_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3507_ = v___x_3858_;
goto v___jp_3506_;
}
v___jp_3859_:
{
lean_object* v___x_3863_; double v___x_3864_; double v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3863_ = lean_io_get_num_heartbeats();
v___x_3864_ = lean_float_of_nat(v___y_3861_);
v___x_3865_ = lean_float_of_nat(v___x_3863_);
v___x_3866_ = lean_box_float(v___x_3864_);
v___x_3867_ = lean_box_float(v___x_3865_);
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3866_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v_a_3862_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v___x_3840_, v___x_3531_, v___x_3841_, v_options_3827_, v___x_3843_, v___y_3860_, v___f_3338_, v___x_3869_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3507_ = v___x_3870_;
goto v___jp_3506_;
}
v___jp_3871_:
{
lean_object* v___x_3872_; lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3934_; 
v___x_3872_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3346_);
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3875_ = v___x_3872_;
v_isShared_3876_ = v_isSharedCheck_3934_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3872_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3934_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; uint8_t v___x_3878_; 
v___x_3877_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3878_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3827_, v___x_3877_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3879_ = lean_io_mono_nanos_now();
v___x_3880_ = l_Lean_SourceInfo_fromRef(v_ref_3838_, v___x_3878_);
v___x_3881_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18));
v___x_3882_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
lean_inc(v___x_3880_);
v___x_3883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3880_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = l_Lean_Syntax_node1(v___x_3880_, v___x_3881_, v___x_3883_);
lean_inc_ref(v_type_3349_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 1);
lean_ctor_set(v___x_3875_, 0, v_type_3349_);
v___x_3886_ = v___x_3875_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_type_3349_);
v___x_3886_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3887_, 0, v___x_3884_);
lean_closure_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3887_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 1);
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
v___y_3845_ = v_a_3873_;
v___y_3846_ = v___x_3879_;
v_a_3847_ = v___x_3894_;
goto v___jp_3844_;
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
v_a_3897_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3888_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3888_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set_tag(v___x_3899_, 0);
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
v___y_3845_ = v_a_3873_;
v___y_3846_ = v___x_3879_;
v_a_3847_ = v___x_3902_;
goto v___jp_3844_;
}
}
}
}
}
else
{
lean_object* v___x_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3906_ = lean_io_get_num_heartbeats();
v___x_3907_ = 0;
v___x_3908_ = l_Lean_SourceInfo_fromRef(v_ref_3838_, v___x_3907_);
v___x_3909_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18));
v___x_3910_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
lean_inc(v___x_3908_);
v___x_3911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3908_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = l_Lean_Syntax_node1(v___x_3908_, v___x_3909_, v___x_3911_);
lean_inc_ref(v_type_3349_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 1);
lean_ctor_set(v___x_3875_, 0, v_type_3349_);
v___x_3914_ = v___x_3875_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_type_3349_);
v___x_3914_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3915_, 0, v___x_3912_);
lean_closure_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3915_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
lean_ctor_set_tag(v___x_3919_, 1);
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
v___y_3860_ = v_a_3873_;
v___y_3861_ = v___x_3906_;
v_a_3862_ = v___x_3922_;
goto v___jp_3859_;
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
v_a_3925_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3916_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3916_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
lean_ctor_set_tag(v___x_3927_, 0);
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
v___y_3860_ = v_a_3873_;
v___y_3861_ = v___x_3906_;
v_a_3862_ = v___x_3930_;
goto v___jp_3859_;
}
}
}
}
}
}
}
}
}
v___jp_3350_:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3359_ = l_Array_append___redArg(v_xs_3334_, v___y_3353_);
lean_dec_ref(v___y_3353_);
v___x_3360_ = 0;
v___x_3361_ = 1;
v___x_3362_ = l_Lean_Meta_mkForallFVars(v___x_3359_, v_type_3349_, v___x_3360_, v___y_3352_, v___y_3352_, v___x_3361_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = l_Lean_Meta_mkLambdaFVars(v___x_3359_, v___y_3351_, v___x_3360_, v___y_3352_, v___x_3360_, v___y_3352_, v___x_3361_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec_ref(v___x_3359_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3374_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3374_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3374_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3369_, 0, v_a_3365_);
lean_ctor_set(v___x_3369_, 1, v___y_3354_);
v___x_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3370_, 0, v_a_3363_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3370_);
v___x_3372_ = v___x_3367_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_a_3363_);
lean_dec(v___y_3354_);
v_a_3375_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3364_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3364_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v___x_3359_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3351_);
v_a_3383_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3362_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3362_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
v___jp_3391_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___y_3395_);
lean_ctor_set(v___x_3403_, 1, v___y_3402_);
lean_inc(v___y_3401_);
v___x_3404_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3401_, v___x_3403_, v___y_3399_, v___y_3392_, v___y_3398_, v___y_3400_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_dec_ref_known(v___x_3404_, 1);
v___y_3351_ = v___y_3393_;
v___y_3352_ = v___y_3394_;
v___y_3353_ = v___y_3396_;
v___y_3354_ = v___y_3397_;
v___y_3355_ = v___y_3399_;
v___y_3356_ = v___y_3392_;
v___y_3357_ = v___y_3398_;
v___y_3358_ = v___y_3400_;
goto v___jp_3350_;
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_type_3349_);
lean_dec_ref(v_xs_3334_);
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
v___jp_3413_:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_nat_dec_eq(v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec(v___y_3423_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v_type_3349_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v___x_3426_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3427_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3426_, v___y_3417_, v___y_3416_, v___y_3421_, v___y_3414_, v___y_3420_, v___y_3422_);
return v___x_3427_;
}
else
{
lean_object* v_toCold_3428_; lean_object* v_options_3429_; uint8_t v_hasTrace_3430_; 
v_toCold_3428_ = lean_ctor_get(v___y_3420_, 0);
v_options_3429_ = lean_ctor_get(v_toCold_3428_, 2);
v_hasTrace_3430_ = lean_ctor_get_uint8(v_options_3429_, sizeof(void*)*1);
if (v_hasTrace_3430_ == 0)
{
lean_dec(v___y_3423_);
lean_dec(v___x_3335_);
v___y_3351_ = v___y_3415_;
v___y_3352_ = v___x_3425_;
v___y_3353_ = v___y_3418_;
v___y_3354_ = v___y_3419_;
v___y_3355_ = v___y_3421_;
v___y_3356_ = v___y_3414_;
v___y_3357_ = v___y_3420_;
v___y_3358_ = v___y_3422_;
goto v___jp_3350_;
}
else
{
lean_object* v_inheritedTraceOptions_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_inheritedTraceOptions_3431_ = lean_ctor_get(v_toCold_3428_, 11);
v___x_3432_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3433_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3434_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3431_, v_options_3429_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_dec(v___y_3423_);
lean_dec(v___x_3335_);
v___y_3351_ = v___y_3415_;
v___y_3352_ = v___x_3425_;
v___y_3353_ = v___y_3418_;
v___y_3354_ = v___y_3419_;
v___y_3355_ = v___y_3421_;
v___y_3356_ = v___y_3414_;
v___y_3357_ = v___y_3420_;
v___y_3358_ = v___y_3422_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3435_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3436_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3415_);
v___x_3437_ = l_Lean_inlineExpr(v___y_3415_, v___x_3436_);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3435_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_nat_dec_eq(v___y_3423_, v___x_3335_);
lean_dec(v___x_3335_);
lean_dec(v___y_3423_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3440_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3418_);
v___x_3441_ = lean_array_to_list(v___y_3418_);
v___x_3442_ = lean_box(0);
v___x_3443_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3441_, v___x_3442_);
v___x_3444_ = l_Lean_MessageData_ofList(v___x_3443_);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3440_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___y_3392_ = v___y_3414_;
v___y_3393_ = v___y_3415_;
v___y_3394_ = v___x_3425_;
v___y_3395_ = v___x_3438_;
v___y_3396_ = v___y_3418_;
v___y_3397_ = v___y_3419_;
v___y_3398_ = v___y_3420_;
v___y_3399_ = v___y_3421_;
v___y_3400_ = v___y_3422_;
v___y_3401_ = v___x_3432_;
v___y_3402_ = v___x_3447_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3392_ = v___y_3414_;
v___y_3393_ = v___y_3415_;
v___y_3394_ = v___x_3425_;
v___y_3395_ = v___x_3438_;
v___y_3396_ = v___y_3418_;
v___y_3397_ = v___y_3419_;
v___y_3398_ = v___y_3420_;
v___y_3399_ = v___y_3421_;
v___y_3400_ = v___y_3422_;
v___y_3401_ = v___x_3432_;
v___y_3402_ = v___x_3448_;
goto v___jp_3391_;
}
}
}
}
}
v___jp_3449_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = lean_box(1);
lean_inc_ref(v___y_3451_);
v___x_3459_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3458_, v_localInst2Index_3340_, v___y_3451_);
v___x_3460_ = lean_array_get_size(v___y_3457_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_size_3461_; 
v_size_3461_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_size_3461_);
v___y_3414_ = v___y_3450_;
v___y_3415_ = v___y_3451_;
v___y_3416_ = v___y_3452_;
v___y_3417_ = v___y_3453_;
v___y_3418_ = v___y_3457_;
v___y_3419_ = v___x_3459_;
v___y_3420_ = v___y_3455_;
v___y_3421_ = v___y_3454_;
v___y_3422_ = v___y_3456_;
v___y_3423_ = v___x_3460_;
v___y_3424_ = v_size_3461_;
goto v___jp_3413_;
}
else
{
lean_inc(v___x_3335_);
v___y_3414_ = v___y_3450_;
v___y_3415_ = v___y_3451_;
v___y_3416_ = v___y_3452_;
v___y_3417_ = v___y_3453_;
v___y_3418_ = v___y_3457_;
v___y_3419_ = v___x_3459_;
v___y_3420_ = v___y_3455_;
v___y_3421_ = v___y_3454_;
v___y_3422_ = v___y_3456_;
v___y_3423_ = v___x_3460_;
v___y_3424_ = v___x_3335_;
goto v___jp_3413_;
}
}
v___jp_3462_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
v___x_3470_ = lean_array_get_size(v_insts_3339_);
v___x_3471_ = lean_mk_empty_array_with_capacity(v___x_3335_);
v___x_3472_ = lean_nat_dec_lt(v___x_3335_, v___x_3470_);
if (v___x_3472_ == 0)
{
v___y_3450_ = v___y_3467_;
v___y_3451_ = v___y_3463_;
v___y_3452_ = v___y_3465_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3466_;
v___y_3455_ = v___y_3468_;
v___y_3456_ = v___y_3469_;
v___y_3457_ = v___x_3471_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; size_t v___x_3476_; size_t v___x_3477_; lean_object* v___x_3478_; 
v___x_3473_ = lean_box(1);
lean_inc_ref(v___x_3471_);
v___x_3474_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_3473_, v___x_3471_);
lean_inc_ref(v___y_3463_);
v___x_3475_ = l_Lean_collectFVars(v___x_3474_, v___y_3463_);
v___x_3476_ = ((size_t)0ULL);
v___x_3477_ = lean_usize_of_nat(v___x_3470_);
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3475_, v_insts_3339_, v___x_3476_, v___x_3477_, v___x_3471_);
lean_dec_ref(v___x_3475_);
v___y_3450_ = v___y_3467_;
v___y_3451_ = v___y_3463_;
v___y_3452_ = v___y_3465_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3466_;
v___y_3455_ = v___y_3468_;
v___y_3456_ = v___y_3469_;
v___y_3457_ = v___x_3478_;
goto v___jp_3449_;
}
}
v___jp_3479_:
{
lean_object* v___x_3481_; 
lean_inc_ref(v_val_3480_);
v___x_3481_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3480_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v___x_3482_; lean_object* v_a_3483_; uint8_t v___x_3484_; 
lean_dec_ref_known(v___x_3481_, 1);
v___x_3482_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3480_, v___y_3344_);
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref(v___x_3482_);
v___x_3484_ = l_Lean_Expr_hasMVar(v_a_3483_);
if (v___x_3484_ == 0)
{
v___y_3463_ = v_a_3483_;
v___y_3464_ = v___y_3341_;
v___y_3465_ = v___y_3342_;
v___y_3466_ = v___y_3343_;
v___y_3467_ = v___y_3344_;
v___y_3468_ = v___y_3345_;
v___y_3469_ = v___y_3346_;
goto v___jp_3462_;
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v___x_3485_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12);
v___x_3486_ = lean_unsigned_to_nat(30u);
v___x_3487_ = l_Lean_inlineExprTrailing(v_a_3483_, v___x_3486_);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3485_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3488_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
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
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v_val_3480_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3498_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3481_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3481_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
v___jp_3506_:
{
if (lean_obj_tag(v___y_3507_) == 0)
{
lean_object* v_a_3508_; 
v_a_3508_ = lean_ctor_get(v___y_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___y_3507_, 1);
v_val_3480_ = v_a_3508_;
goto v___jp_3479_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3509_ = lean_ctor_get(v___y_3507_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___y_3507_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___y_3507_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___y_3507_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
v___jp_3517_:
{
if (lean_obj_tag(v___y_3518_) == 0)
{
lean_object* v_a_3519_; 
v_a_3519_ = lean_ctor_get(v___y_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___y_3518_, 1);
v_val_3480_ = v_a_3519_;
goto v___jp_3479_;
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec_ref(v_xs_3334_);
v_a_3520_ = lean_ctor_get(v___y_3518_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___y_3518_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___y_3518_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___y_3518_);
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
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object* v_inductiveTypeName_3945_, lean_object* v_us_3946_, lean_object* v_xs_3947_, lean_object* v___x_3948_, lean_object* v_ctorName_3949_, lean_object* v___x_3950_, lean_object* v___f_3951_, lean_object* v_insts_3952_, lean_object* v_localInst2Index_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_3945_, v_us_3946_, v_xs_3947_, v___x_3948_, v_ctorName_3949_, v___x_3950_, v___f_3951_, v_insts_3952_, v_localInst2Index_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec_ref(v_insts_3952_);
lean_dec_ref(v___x_3950_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___lam__0(lean_object* v_k_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; 
lean_inc(v___y_3964_);
lean_inc_ref(v___y_3963_);
v___x_3970_ = lean_apply_7(v_k_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, lean_box(0));
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___lam__0(v_k_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg(lean_object* v_bs_3980_, lean_object* v_k_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___f_3989_; lean_object* v___x_3990_; 
lean_inc(v___y_3983_);
lean_inc_ref(v___y_3982_);
v___f_3989_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3989_, 0, v_k_3981_);
lean_closure_set(v___f_3989_, 1, v___y_3982_);
lean_closure_set(v___f_3989_, 2, v___y_3983_);
v___x_3990_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3980_, v___f_3989_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_3990_) == 0)
{
return v___x_3990_;
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg___boxed(lean_object* v_bs_3999_, lean_object* v_k_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg(v_bs_3999_, v_k_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec_ref(v_bs_3999_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__9(size_t v_sz_4009_, size_t v_i_4010_, lean_object* v_bs_4011_){
_start:
{
uint8_t v___x_4012_; 
v___x_4012_ = lean_usize_dec_lt(v_i_4010_, v_sz_4009_);
if (v___x_4012_ == 0)
{
return v_bs_4011_;
}
else
{
lean_object* v_v_4013_; lean_object* v___x_4014_; lean_object* v_bs_x27_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; size_t v___x_4020_; size_t v___x_4021_; lean_object* v___x_4022_; 
v_v_4013_ = lean_array_uget(v_bs_4011_, v_i_4010_);
v___x_4014_ = lean_unsigned_to_nat(0u);
v_bs_x27_4015_ = lean_array_uset(v_bs_4011_, v_i_4010_, v___x_4014_);
v___x_4016_ = l_Lean_Expr_fvarId_x21(v_v_4013_);
lean_dec(v_v_4013_);
v___x_4017_ = 1;
v___x_4018_ = lean_box(v___x_4017_);
v___x_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4016_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = ((size_t)1ULL);
v___x_4021_ = lean_usize_add(v_i_4010_, v___x_4020_);
v___x_4022_ = lean_array_uset(v_bs_x27_4015_, v_i_4010_, v___x_4019_);
v_i_4010_ = v___x_4021_;
v_bs_4011_ = v___x_4022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__9___boxed(lean_object* v_sz_4024_, lean_object* v_i_4025_, lean_object* v_bs_4026_){
_start:
{
size_t v_sz_boxed_4027_; size_t v_i_boxed_4028_; lean_object* v_res_4029_; 
v_sz_boxed_4027_ = lean_unbox_usize(v_sz_4024_);
lean_dec(v_sz_4024_);
v_i_boxed_4028_ = lean_unbox_usize(v_i_4025_);
lean_dec(v_i_4025_);
v_res_4029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__9(v_sz_boxed_4027_, v_i_boxed_4028_, v_bs_4026_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_bs_4030_, lean_object* v_k_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
size_t v_sz_4039_; size_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_sz_4039_ = lean_array_size(v_bs_4030_);
v___x_4040_ = ((size_t)0ULL);
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__9(v_sz_4039_, v___x_4040_, v_bs_4030_);
v___x_4042_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg(v___x_4041_, v_k_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec_ref(v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_bs_4043_, lean_object* v_k_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_bs_4043_, v_k_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4053_, lean_object* v_inductiveTypeName_4054_, lean_object* v_us_4055_, lean_object* v_ctorName_4056_, lean_object* v___f_4057_, uint8_t v_addHypotheses_4058_, lean_object* v_xs_4059_, lean_object* v_x_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___f_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4068_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4059_, 2);
v___x_4069_ = l_Array_toSubarray___redArg(v_xs_4059_, v___x_4068_, v_numParams_4053_);
v___x_4070_ = l_Subarray_copy___redArg(v___x_4069_);
lean_inc_ref(v___x_4070_);
v___f_4071_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 16, 7);
lean_closure_set(v___f_4071_, 0, v_inductiveTypeName_4054_);
lean_closure_set(v___f_4071_, 1, v_us_4055_);
lean_closure_set(v___f_4071_, 2, v_xs_4059_);
lean_closure_set(v___f_4071_, 3, v___x_4068_);
lean_closure_set(v___f_4071_, 4, v_ctorName_4056_);
lean_closure_set(v___f_4071_, 5, v___x_4070_);
lean_closure_set(v___f_4071_, 6, v___f_4057_);
v___x_4072_ = lean_box(v_addHypotheses_4058_);
v___x_4073_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4073_, 0, v___x_4072_);
lean_closure_set(v___x_4073_, 1, lean_box(0));
lean_closure_set(v___x_4073_, 2, v___x_4070_);
lean_closure_set(v___x_4073_, 3, v___f_4071_);
v___x_4074_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_xs_4059_, v___x_4073_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4075_, lean_object* v_inductiveTypeName_4076_, lean_object* v_us_4077_, lean_object* v_ctorName_4078_, lean_object* v___f_4079_, lean_object* v_addHypotheses_4080_, lean_object* v_xs_4081_, lean_object* v_x_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
uint8_t v_addHypotheses_boxed_4090_; lean_object* v_res_4091_; 
v_addHypotheses_boxed_4090_ = lean_unbox(v_addHypotheses_4080_);
v_res_4091_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4075_, v_inductiveTypeName_4076_, v_us_4077_, v_ctorName_4078_, v___f_4079_, v_addHypotheses_boxed_4090_, v_xs_4081_, v_x_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec_ref(v_x_4082_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
if (lean_obj_tag(v_a_4092_) == 0)
{
lean_object* v___x_4094_; 
v___x_4094_ = l_List_reverse___redArg(v_a_4093_);
return v___x_4094_;
}
else
{
lean_object* v_head_4095_; lean_object* v_tail_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4105_; 
v_head_4095_ = lean_ctor_get(v_a_4092_, 0);
v_tail_4096_ = lean_ctor_get(v_a_4092_, 1);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_a_4092_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4098_ = v_a_4092_;
v_isShared_4099_ = v_isSharedCheck_4105_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_tail_4096_);
lean_inc(v_head_4095_);
lean_dec(v_a_4092_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4105_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; lean_object* v___x_4102_; 
v___x_4100_ = l_Lean_Level_param___override(v_head_4095_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 1, v_a_4093_);
lean_ctor_set(v___x_4098_, 0, v___x_4100_);
v___x_4102_ = v___x_4098_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4100_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v_a_4093_);
v___x_4102_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
v_a_4092_ = v_tail_4096_;
v_a_4093_ = v___x_4102_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4107_, lean_object* v_ctorName_4108_, uint8_t v_addHypotheses_4109_, lean_object* v_indVal_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_){
_start:
{
lean_object* v_toConstantVal_4118_; lean_object* v_numParams_4119_; lean_object* v_levelParams_4120_; lean_object* v_type_4121_; lean_object* v___f_4122_; lean_object* v___x_4123_; lean_object* v_us_4124_; lean_object* v___x_4125_; lean_object* v___f_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; 
v_toConstantVal_4118_ = lean_ctor_get(v_indVal_4110_, 0);
lean_inc_ref(v_toConstantVal_4118_);
v_numParams_4119_ = lean_ctor_get(v_indVal_4110_, 1);
lean_inc(v_numParams_4119_);
lean_dec_ref(v_indVal_4110_);
v_levelParams_4120_ = lean_ctor_get(v_toConstantVal_4118_, 1);
lean_inc(v_levelParams_4120_);
v_type_4121_ = lean_ctor_get(v_toConstantVal_4118_, 2);
lean_inc_ref(v_type_4121_);
lean_dec_ref(v_toConstantVal_4118_);
v___f_4122_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4123_ = lean_box(0);
v_us_4124_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4120_, v___x_4123_);
v___x_4125_ = lean_box(v_addHypotheses_4109_);
v___f_4126_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 15, 6);
lean_closure_set(v___f_4126_, 0, v_numParams_4119_);
lean_closure_set(v___f_4126_, 1, v_inductiveTypeName_4107_);
lean_closure_set(v___f_4126_, 2, v_us_4124_);
lean_closure_set(v___f_4126_, 3, v_ctorName_4108_);
lean_closure_set(v___f_4126_, 4, v___f_4122_);
lean_closure_set(v___f_4126_, 5, v___x_4125_);
v___x_4127_ = 0;
v___x_4128_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__9___redArg(v_type_4121_, v___f_4126_, v___x_4127_, v___x_4127_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4129_, lean_object* v_ctorName_4130_, lean_object* v_addHypotheses_4131_, lean_object* v_indVal_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
uint8_t v_addHypotheses_boxed_4140_; lean_object* v_res_4141_; 
v_addHypotheses_boxed_4140_ = lean_unbox(v_addHypotheses_4131_);
v_res_4141_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4129_, v_ctorName_4130_, v_addHypotheses_boxed_4140_, v_indVal_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
return v_res_4141_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v_00_u03b2_4142_, lean_object* v_k_4143_, lean_object* v_t_4144_){
_start:
{
uint8_t v___x_4145_; 
v___x_4145_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___redArg(v_k_4143_, v_t_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v_00_u03b2_4146_, lean_object* v_k_4147_, lean_object* v_t_4148_){
_start:
{
uint8_t v_res_4149_; lean_object* v_r_4150_; 
v_res_4149_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_00_u03b2_4146_, v_k_4147_, v_t_4148_);
lean_dec(v_t_4148_);
lean_dec(v_k_4147_);
v_r_4150_ = lean_box(v_res_4149_);
return v_r_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10(lean_object* v_00_u03b1_4151_, lean_object* v_bs_4152_, lean_object* v_k_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___redArg(v_bs_4152_, v_k_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4162_, lean_object* v_bs_4163_, lean_object* v_k_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_spec__10(v_00_u03b1_4162_, v_bs_4163_, v_k_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec_ref(v_bs_4163_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_4173_, lean_object* v_bs_4174_, lean_object* v_k_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_bs_4174_, v_k_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_4184_, lean_object* v_bs_4185_, lean_object* v_k_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_4184_, v_bs_4185_, v_k_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4195_, lean_object* v_levelParams_4196_, lean_object* v_type_4197_, lean_object* v_value_4198_, lean_object* v_hints_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v___x_4202_; uint8_t v___y_4204_; lean_object* v_env_4212_; uint8_t v___x_4213_; 
v___x_4202_ = lean_st_ref_get(v___y_4200_);
v_env_4212_ = lean_ctor_get(v___x_4202_, 0);
lean_inc_ref_n(v_env_4212_, 2);
lean_dec(v___x_4202_);
v___x_4213_ = l_Lean_Environment_hasUnsafe(v_env_4212_, v_type_4197_);
if (v___x_4213_ == 0)
{
uint8_t v___x_4214_; 
v___x_4214_ = l_Lean_Environment_hasUnsafe(v_env_4212_, v_value_4198_);
if (v___x_4214_ == 0)
{
uint8_t v___x_4215_; 
v___x_4215_ = 1;
v___y_4204_ = v___x_4215_;
goto v___jp_4203_;
}
else
{
goto v___jp_4210_;
}
}
else
{
lean_dec_ref(v_env_4212_);
goto v___jp_4210_;
}
v___jp_4203_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_inc(v_name_4195_);
v___x_4205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4205_, 0, v_name_4195_);
lean_ctor_set(v___x_4205_, 1, v_levelParams_4196_);
lean_ctor_set(v___x_4205_, 2, v_type_4197_);
v___x_4206_ = lean_box(0);
v___x_4207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4207_, 0, v_name_4195_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4208_, 0, v___x_4205_);
lean_ctor_set(v___x_4208_, 1, v_value_4198_);
lean_ctor_set(v___x_4208_, 2, v_hints_4199_);
lean_ctor_set(v___x_4208_, 3, v___x_4207_);
lean_ctor_set_uint8(v___x_4208_, sizeof(void*)*4, v___y_4204_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
v___jp_4210_:
{
uint8_t v___x_4211_; 
v___x_4211_ = 0;
v___y_4204_ = v___x_4211_;
goto v___jp_4203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4216_, lean_object* v_levelParams_4217_, lean_object* v_type_4218_, lean_object* v_value_4219_, lean_object* v_hints_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4216_, v_levelParams_4217_, v_type_4218_, v_value_4219_, v_hints_4220_, v___y_4221_);
lean_dec(v___y_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4224_, lean_object* v_levelParams_4225_, lean_object* v_type_4226_, lean_object* v_value_4227_, lean_object* v_hints_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4224_, v_levelParams_4225_, v_type_4226_, v_value_4227_, v_hints_4228_, v___y_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4237_, lean_object* v_levelParams_4238_, lean_object* v_type_4239_, lean_object* v_value_4240_, lean_object* v_hints_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4237_, v_levelParams_4238_, v_type_4239_, v_value_4240_, v_hints_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
return v_res_4270_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4271_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0);
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg(){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__1);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___boxed(lean_object* v___dummy_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg();
return v_res_4277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4280_ = l_Lean_stringToMessageData(v___x_4279_);
return v___x_4280_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4283_ = l_Lean_stringToMessageData(v___x_4282_);
return v___x_4283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4(void){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0);
v___x_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4284_);
return v___x_4285_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4);
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
return v___x_4287_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6(void){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg();
return v___x_4288_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4);
v___x_4290_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6);
v___x_4291_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
lean_ctor_set(v___x_4291_, 1, v___x_4289_);
lean_ctor_set(v___x_4291_, 2, v___x_4289_);
lean_ctor_set(v___x_4291_, 3, v___x_4289_);
lean_ctor_set(v___x_4291_, 4, v___x_4289_);
lean_ctor_set(v___x_4291_, 5, v___x_4289_);
lean_ctor_set(v___x_4291_, 6, v___x_4289_);
return v___x_4291_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__9(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__8));
v___x_4294_ = l_Lean_stringToMessageData(v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4295_, lean_object* v___x_4296_, lean_object* v_inductiveTypeName_4297_, uint8_t v___x_4298_, lean_object* v___x_4299_, lean_object* v___f_4300_, lean_object* v_ctorName_4301_, uint8_t v_addHypotheses_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___y_4311_; lean_object* v___x_4314_; 
lean_inc(v_inductiveTypeName_4297_);
v___x_4314_ = l_Lean_Elab_Deriving_mkContext(v___x_4295_, v___x_4296_, v_inductiveTypeName_4297_, v___x_4298_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_toCold_4315_; lean_object* v_a_4316_; lean_object* v_options_4317_; lean_object* v_currNamespace_4318_; lean_object* v_inheritedTraceOptions_4319_; lean_object* v_instName_4320_; lean_object* v_auxFunNames_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; uint8_t v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; uint8_t v___y_4376_; uint8_t v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___x_4430_; 
v_toCold_4315_ = lean_ctor_get(v___y_4307_, 0);
v_a_4316_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4314_, 1);
v_options_4317_ = lean_ctor_get(v_toCold_4315_, 2);
v_currNamespace_4318_ = lean_ctor_get(v_toCold_4315_, 4);
v_inheritedTraceOptions_4319_ = lean_ctor_get(v_toCold_4315_, 11);
v_instName_4320_ = lean_ctor_get(v_a_4316_, 0);
lean_inc(v_instName_4320_);
v_auxFunNames_4321_ = lean_ctor_get(v_a_4316_, 2);
lean_inc_ref(v_auxFunNames_4321_);
lean_dec(v_a_4316_);
v___x_4322_ = lean_unsigned_to_nat(0u);
v___x_4323_ = lean_array_get(v___x_4299_, v_auxFunNames_4321_, v___x_4322_);
lean_dec_ref(v_auxFunNames_4321_);
lean_inc(v_currNamespace_4318_);
v___x_4324_ = l_Lean_Name_append(v_currNamespace_4318_, v___x_4323_);
lean_inc(v_inductiveTypeName_4297_);
v___x_4430_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4297_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v_a_4433_; lean_object* v___y_4505_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc_n(v_a_4431_, 2);
lean_dec_ref_known(v___x_4430_, 1);
v___x_4527_ = lean_box(v_addHypotheses_4302_);
lean_inc(v_inductiveTypeName_4297_);
v___x_4528_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4528_, 0, v_inductiveTypeName_4297_);
lean_closure_set(v___x_4528_, 1, v_ctorName_4301_);
lean_closure_set(v___x_4528_, 2, v___x_4527_);
lean_closure_set(v___x_4528_, 3, v_a_4431_);
lean_inc(v___x_4324_);
v___x_4529_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4324_, v___x_4528_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; 
lean_dec_ref(v___f_4300_);
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v_a_4433_ = v_a_4530_;
goto v___jp_4432_;
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4561_; 
v_a_4531_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4533_ = v___x_4529_;
v_isShared_4534_ = v_isSharedCheck_4561_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4529_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4561_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
uint8_t v___x_4535_; 
v___x_4535_ = l_Lean_Exception_isInterrupt(v_a_4531_);
if (v___x_4535_ == 0)
{
uint8_t v___x_4536_; 
lean_inc(v_a_4531_);
v___x_4536_ = l_Lean_Exception_isRuntime(v_a_4531_);
if (v___x_4536_ == 0)
{
uint8_t v_hasTrace_4537_; 
lean_del_object(v___x_4533_);
v_hasTrace_4537_ = lean_ctor_get_uint8(v_options_4317_, sizeof(void*)*1);
if (v_hasTrace_4537_ == 0)
{
lean_dec(v_a_4531_);
goto v___jp_4524_;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4538_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4539_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4319_, v_options_4317_, v___x_4539_);
if (v___x_4540_ == 0)
{
lean_dec(v_a_4531_);
goto v___jp_4524_;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4541_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__9);
v___x_4542_ = l_Lean_Exception_toMessageData(v_a_4531_);
v___x_4543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4541_);
lean_ctor_set(v___x_4543_, 1, v___x_4542_);
v___x_4544_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4538_, v___x_4543_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4546_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_a_4545_);
lean_dec_ref_known(v___x_4544_, 1);
lean_inc(v___y_4308_);
lean_inc_ref(v___y_4307_);
lean_inc(v___y_4306_);
lean_inc_ref(v___y_4305_);
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
v___x_4546_ = lean_apply_8(v___f_4300_, v_a_4545_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, lean_box(0));
v___y_4505_ = v___x_4546_;
goto v___jp_4504_;
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec(v_a_4431_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v___f_4300_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4547_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4544_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4544_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
}
}
else
{
lean_object* v___x_4556_; 
lean_dec(v_a_4431_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v___f_4300_);
lean_dec(v_inductiveTypeName_4297_);
if (v_isShared_4534_ == 0)
{
v___x_4556_ = v___x_4533_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4531_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
else
{
lean_object* v___x_4559_; 
lean_dec(v_a_4431_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v___f_4300_);
lean_dec(v_inductiveTypeName_4297_);
if (v_isShared_4534_ == 0)
{
v___x_4559_ = v___x_4533_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4531_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
v___jp_4432_:
{
lean_object* v_snd_4434_; lean_object* v_fst_4435_; lean_object* v_fst_4436_; lean_object* v_snd_4437_; lean_object* v___x_4438_; lean_object* v_toConstantVal_4439_; lean_object* v_env_4440_; lean_object* v_levelParams_4441_; uint32_t v___x_4442_; uint32_t v___x_4443_; uint32_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4503_; 
v_snd_4434_ = lean_ctor_get(v_a_4433_, 1);
lean_inc(v_snd_4434_);
v_fst_4435_ = lean_ctor_get(v_a_4433_, 0);
lean_inc(v_fst_4435_);
lean_dec_ref(v_a_4433_);
v_fst_4436_ = lean_ctor_get(v_snd_4434_, 0);
lean_inc_n(v_fst_4436_, 2);
v_snd_4437_ = lean_ctor_get(v_snd_4434_, 1);
lean_inc(v_snd_4437_);
lean_dec(v_snd_4434_);
v___x_4438_ = lean_st_ref_get(v___y_4308_);
v_toConstantVal_4439_ = lean_ctor_get(v_a_4431_, 0);
lean_inc_ref(v_toConstantVal_4439_);
lean_dec(v_a_4431_);
v_env_4440_ = lean_ctor_get(v___x_4438_, 0);
lean_inc_ref(v_env_4440_);
lean_dec(v___x_4438_);
v_levelParams_4441_ = lean_ctor_get(v_toConstantVal_4439_, 1);
lean_inc(v_levelParams_4441_);
lean_dec_ref(v_toConstantVal_4439_);
v___x_4442_ = l_Lean_getMaxHeight(v_env_4440_, v_fst_4436_);
v___x_4443_ = 1;
v___x_4444_ = lean_uint32_add(v___x_4442_, v___x_4443_);
v___x_4445_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4445_, 0, v___x_4444_);
lean_inc(v___x_4324_);
v___x_4446_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4324_, v_levelParams_4441_, v_fst_4435_, v_fst_4436_, v___x_4445_, v___y_4308_);
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4503_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4503_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set_tag(v___x_4449_, 1);
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
uint8_t v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = 0;
v___x_4454_ = l_Lean_addDecl(v___x_4452_, v___x_4453_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4455_; lean_object* v_env_4456_; uint8_t v___x_4457_; 
lean_dec_ref_known(v___x_4454_, 1);
v___x_4455_ = lean_st_ref_get(v___y_4308_);
v_env_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc_ref(v_env_4456_);
lean_dec(v___x_4455_);
lean_inc(v_inductiveTypeName_4297_);
v___x_4457_ = l_Lean_isMarkedMeta(v_env_4456_, v_inductiveTypeName_4297_);
if (v___x_4457_ == 0)
{
v___y_4415_ = v___x_4453_;
v___y_4416_ = v_snd_4437_;
v___y_4417_ = v___y_4303_;
v___y_4418_ = v___y_4304_;
v___y_4419_ = v___y_4305_;
v___y_4420_ = v___y_4306_;
v___y_4421_ = v___y_4307_;
v___y_4422_ = v___y_4308_;
goto v___jp_4414_;
}
else
{
lean_object* v___x_4458_; lean_object* v_env_4459_; lean_object* v_nextMacroScope_4460_; lean_object* v_ngen_4461_; lean_object* v_auxDeclNGen_4462_; lean_object* v_traceState_4463_; lean_object* v_recordedDeps_4464_; lean_object* v_messages_4465_; lean_object* v_infoState_4466_; lean_object* v_snapshotTasks_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4492_; 
v___x_4458_ = lean_st_ref_take(v___y_4308_);
v_env_4459_ = lean_ctor_get(v___x_4458_, 0);
v_nextMacroScope_4460_ = lean_ctor_get(v___x_4458_, 1);
v_ngen_4461_ = lean_ctor_get(v___x_4458_, 2);
v_auxDeclNGen_4462_ = lean_ctor_get(v___x_4458_, 3);
v_traceState_4463_ = lean_ctor_get(v___x_4458_, 4);
v_recordedDeps_4464_ = lean_ctor_get(v___x_4458_, 6);
v_messages_4465_ = lean_ctor_get(v___x_4458_, 7);
v_infoState_4466_ = lean_ctor_get(v___x_4458_, 8);
v_snapshotTasks_4467_ = lean_ctor_get(v___x_4458_, 9);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4492_ == 0)
{
lean_object* v_unused_4493_; 
v_unused_4493_ = lean_ctor_get(v___x_4458_, 5);
lean_dec(v_unused_4493_);
v___x_4469_ = v___x_4458_;
v_isShared_4470_ = v_isSharedCheck_4492_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_snapshotTasks_4467_);
lean_inc(v_infoState_4466_);
lean_inc(v_messages_4465_);
lean_inc(v_recordedDeps_4464_);
lean_inc(v_traceState_4463_);
lean_inc(v_auxDeclNGen_4462_);
lean_inc(v_ngen_4461_);
lean_inc(v_nextMacroScope_4460_);
lean_inc(v_env_4459_);
lean_dec(v___x_4458_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4492_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4474_; 
lean_inc(v___x_4324_);
v___x_4471_ = l_Lean_markMeta(v_env_4459_, v___x_4324_);
v___x_4472_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 5, v___x_4472_);
lean_ctor_set(v___x_4469_, 0, v___x_4471_);
v___x_4474_ = v___x_4469_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4491_, 1, v_nextMacroScope_4460_);
lean_ctor_set(v_reuseFailAlloc_4491_, 2, v_ngen_4461_);
lean_ctor_set(v_reuseFailAlloc_4491_, 3, v_auxDeclNGen_4462_);
lean_ctor_set(v_reuseFailAlloc_4491_, 4, v_traceState_4463_);
lean_ctor_set(v_reuseFailAlloc_4491_, 5, v___x_4472_);
lean_ctor_set(v_reuseFailAlloc_4491_, 6, v_recordedDeps_4464_);
lean_ctor_set(v_reuseFailAlloc_4491_, 7, v_messages_4465_);
lean_ctor_set(v_reuseFailAlloc_4491_, 8, v_infoState_4466_);
lean_ctor_set(v_reuseFailAlloc_4491_, 9, v_snapshotTasks_4467_);
v___x_4474_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v_mctx_4477_; lean_object* v_zetaDeltaFVarIds_4478_; lean_object* v_postponed_4479_; lean_object* v_diag_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4489_; 
v___x_4475_ = lean_st_ref_put(v___y_4308_, v___x_4474_);
v___x_4476_ = lean_st_ref_take(v___y_4306_);
v_mctx_4477_ = lean_ctor_get(v___x_4476_, 0);
v_zetaDeltaFVarIds_4478_ = lean_ctor_get(v___x_4476_, 2);
v_postponed_4479_ = lean_ctor_get(v___x_4476_, 3);
v_diag_4480_ = lean_ctor_get(v___x_4476_, 4);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; 
v_unused_4490_ = lean_ctor_get(v___x_4476_, 1);
lean_dec(v_unused_4490_);
v___x_4482_ = v___x_4476_;
v_isShared_4483_ = v_isSharedCheck_4489_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_diag_4480_);
lean_inc(v_postponed_4479_);
lean_inc(v_zetaDeltaFVarIds_4478_);
lean_inc(v_mctx_4477_);
lean_dec(v___x_4476_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4489_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4484_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 1, v___x_4484_);
v___x_4486_ = v___x_4482_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_mctx_4477_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4488_, 2, v_zetaDeltaFVarIds_4478_);
lean_ctor_set(v_reuseFailAlloc_4488_, 3, v_postponed_4479_);
lean_ctor_set(v_reuseFailAlloc_4488_, 4, v_diag_4480_);
v___x_4486_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; 
v___x_4487_ = lean_st_ref_put(v___y_4306_, v___x_4486_);
v___y_4415_ = v___x_4453_;
v___y_4416_ = v_snd_4437_;
v___y_4417_ = v___y_4303_;
v___y_4418_ = v___y_4304_;
v___y_4419_ = v___y_4305_;
v___y_4420_ = v___y_4306_;
v___y_4421_ = v___y_4307_;
v___y_4422_ = v___y_4308_;
goto v___jp_4414_;
}
}
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_snd_4437_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4494_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4454_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4454_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
}
v___jp_4504_:
{
if (lean_obj_tag(v___y_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4515_; 
v_a_4506_ = lean_ctor_get(v___y_4505_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___y_4505_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4508_ = v___y_4505_;
v_isShared_4509_ = v_isSharedCheck_4515_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___y_4505_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4515_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
if (lean_obj_tag(v_a_4506_) == 0)
{
lean_object* v_a_4510_; lean_object* v___x_4512_; 
lean_dec(v_a_4431_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4510_ = lean_ctor_get(v_a_4506_, 0);
lean_inc(v_a_4510_);
lean_dec_ref_known(v_a_4506_, 1);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v_a_4510_);
v___x_4512_ = v___x_4508_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
else
{
lean_object* v_a_4514_; 
lean_del_object(v___x_4508_);
v_a_4514_ = lean_ctor_get(v_a_4506_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v_a_4506_, 1);
v_a_4433_ = v_a_4514_;
goto v___jp_4432_;
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec(v_a_4431_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4516_ = lean_ctor_get(v___y_4505_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___y_4505_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___y_4505_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___y_4505_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
v___jp_4524_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = lean_box(0);
lean_inc(v___y_4308_);
lean_inc_ref(v___y_4307_);
lean_inc(v___y_4306_);
lean_inc_ref(v___y_4305_);
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
v___x_4526_ = lean_apply_8(v___f_4300_, v___x_4525_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, lean_box(0));
v___y_4505_ = v___x_4526_;
goto v___jp_4504_;
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v_ctorName_4301_);
lean_dec_ref(v___f_4300_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4562_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4430_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4430_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
v___jp_4325_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = l_Lean_mkIdent(v_instName_4320_);
v___x_4335_ = l_Lean_mkCIdent(v___x_4324_);
v___x_4336_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4297_, v___x_4334_, v___y_4327_, v___x_4335_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v___y_4327_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_toCold_4337_; lean_object* v_options_4338_; uint8_t v_hasTrace_4339_; 
v_toCold_4337_ = lean_ctor_get(v___y_4332_, 0);
v_options_4338_ = lean_ctor_get(v_toCold_4337_, 2);
v_hasTrace_4339_ = lean_ctor_get_uint8(v_options_4338_, sizeof(void*)*1);
if (v_hasTrace_4339_ == 0)
{
lean_object* v_a_4340_; 
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4326_);
v_a_4340_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4336_, 1);
v___y_4311_ = v_a_4340_;
goto v___jp_4310_;
}
else
{
lean_object* v_a_4341_; lean_object* v_inheritedTraceOptions_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v_a_4341_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4341_);
lean_dec_ref_known(v___x_4336_, 1);
v_inheritedTraceOptions_4342_ = lean_ctor_get(v_toCold_4337_, 11);
v___x_4343_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4326_);
v___x_4344_ = l_Lean_Name_append(v___x_4343_, v___y_4326_);
v___x_4345_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4344_);
lean_dec(v___x_4344_);
if (v___x_4345_ == 0)
{
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4326_);
v___y_4311_ = v_a_4341_;
goto v___jp_4310_;
}
else
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4346_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4341_);
v___x_4347_ = l_Lean_MessageData_ofSyntax(v_a_4341_);
v___x_4348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4346_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
v___x_4349_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4326_, v___x_4348_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_dec_ref_known(v___x_4349_, 1);
v___y_4311_ = v_a_4341_;
goto v___jp_4310_;
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec(v_a_4341_);
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4349_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4349_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4326_);
v_a_4358_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4336_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4336_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
v___jp_4366_:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_compileDecls(v___y_4369_, v___y_4376_, v___y_4373_, v___y_4375_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v___x_4378_; 
lean_dec_ref_known(v___x_4377_, 1);
lean_inc(v___x_4324_);
v___x_4378_ = l_Lean_enableRealizationsForConst(v___x_4324_, v___y_4373_, v___y_4375_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_toCold_4379_; lean_object* v_options_4380_; lean_object* v_inheritedTraceOptions_4381_; uint8_t v_hasTrace_4382_; lean_object* v___x_4383_; 
lean_dec_ref_known(v___x_4378_, 1);
v_toCold_4379_ = lean_ctor_get(v___y_4373_, 0);
v_options_4380_ = lean_ctor_get(v_toCold_4379_, 2);
v_inheritedTraceOptions_4381_ = lean_ctor_get(v_toCold_4379_, 11);
v_hasTrace_4382_ = lean_ctor_get_uint8(v_options_4380_, sizeof(void*)*1);
v___x_4383_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4382_ == 0)
{
v___y_4326_ = v___x_4383_;
v___y_4327_ = v___y_4374_;
v___y_4328_ = v___y_4368_;
v___y_4329_ = v___y_4372_;
v___y_4330_ = v___y_4367_;
v___y_4331_ = v___y_4371_;
v___y_4332_ = v___y_4373_;
v___y_4333_ = v___y_4375_;
goto v___jp_4325_;
}
else
{
lean_object* v___x_4384_; uint8_t v___x_4385_; 
v___x_4384_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4385_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4381_, v_options_4380_, v___x_4384_);
if (v___x_4385_ == 0)
{
v___y_4326_ = v___x_4383_;
v___y_4327_ = v___y_4374_;
v___y_4328_ = v___y_4368_;
v___y_4329_ = v___y_4372_;
v___y_4330_ = v___y_4367_;
v___y_4331_ = v___y_4371_;
v___y_4332_ = v___y_4373_;
v___y_4333_ = v___y_4375_;
goto v___jp_4325_;
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4386_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4324_);
v___x_4387_ = l_Lean_MessageData_ofConstName(v___x_4324_, v___y_4370_);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4386_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4383_, v___x_4388_, v___y_4367_, v___y_4371_, v___y_4373_, v___y_4375_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_dec_ref_known(v___x_4389_, 1);
v___y_4326_ = v___x_4383_;
v___y_4327_ = v___y_4374_;
v___y_4328_ = v___y_4368_;
v___y_4329_ = v___y_4372_;
v___y_4330_ = v___y_4367_;
v___y_4331_ = v___y_4371_;
v___y_4332_ = v___y_4373_;
v___y_4333_ = v___y_4375_;
goto v___jp_4325_;
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4398_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4378_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4378_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
lean_dec(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___x_4324_);
lean_dec(v_instName_4320_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4406_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4377_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4377_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
v___jp_4414_:
{
lean_object* v___x_4423_; lean_object* v_env_4424_; uint8_t v_isNoncomputableSection_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4423_ = lean_st_ref_get(v___y_4422_);
v_env_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc_ref(v_env_4424_);
lean_dec(v___x_4423_);
v_isNoncomputableSection_4425_ = lean_ctor_get_uint8(v___y_4417_, sizeof(void*)*8 + 4);
v___x_4426_ = lean_unsigned_to_nat(1u);
v___x_4427_ = lean_mk_empty_array_with_capacity(v___x_4426_);
lean_inc(v___x_4324_);
v___x_4428_ = lean_array_push(v___x_4427_, v___x_4324_);
if (v_isNoncomputableSection_4425_ == 0)
{
lean_dec_ref(v_env_4424_);
v___y_4367_ = v___y_4419_;
v___y_4368_ = v___y_4417_;
v___y_4369_ = v___x_4428_;
v___y_4370_ = v___y_4415_;
v___y_4371_ = v___y_4420_;
v___y_4372_ = v___y_4418_;
v___y_4373_ = v___y_4421_;
v___y_4374_ = v___y_4416_;
v___y_4375_ = v___y_4422_;
v___y_4376_ = v___x_4298_;
goto v___jp_4366_;
}
else
{
uint8_t v___x_4429_; 
lean_inc(v___x_4324_);
v___x_4429_ = l_Lean_isMarkedMeta(v_env_4424_, v___x_4324_);
v___y_4367_ = v___y_4419_;
v___y_4368_ = v___y_4417_;
v___y_4369_ = v___x_4428_;
v___y_4370_ = v___y_4415_;
v___y_4371_ = v___y_4420_;
v___y_4372_ = v___y_4418_;
v___y_4373_ = v___y_4421_;
v___y_4374_ = v___y_4416_;
v___y_4375_ = v___y_4422_;
v___y_4376_ = v___x_4429_;
goto v___jp_4366_;
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v_ctorName_4301_);
lean_dec_ref(v___f_4300_);
lean_dec(v_inductiveTypeName_4297_);
v_a_4570_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4314_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4314_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
v___jp_4310_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4312_, 0, v___y_4311_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4578_, lean_object* v___x_4579_, lean_object* v_inductiveTypeName_4580_, lean_object* v___x_4581_, lean_object* v___x_4582_, lean_object* v___f_4583_, lean_object* v_ctorName_4584_, lean_object* v_addHypotheses_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
uint8_t v___x_16830__boxed_4593_; uint8_t v_addHypotheses_boxed_4594_; lean_object* v_res_4595_; 
v___x_16830__boxed_4593_ = lean_unbox(v___x_4581_);
v_addHypotheses_boxed_4594_ = lean_unbox(v_addHypotheses_4585_);
v_res_4595_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4578_, v___x_4579_, v_inductiveTypeName_4580_, v___x_16830__boxed_4593_, v___x_4582_, v___f_4583_, v_ctorName_4584_, v_addHypotheses_boxed_4594_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
lean_dec(v___x_4582_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___lam__0(lean_object* v___y_4596_, uint8_t v_isExporting_4597_, lean_object* v___x_4598_, lean_object* v___y_4599_, lean_object* v___x_4600_, lean_object* v_a_x3f_4601_){
_start:
{
lean_object* v___x_4603_; lean_object* v_env_4604_; lean_object* v_nextMacroScope_4605_; lean_object* v_ngen_4606_; lean_object* v_auxDeclNGen_4607_; lean_object* v_traceState_4608_; lean_object* v_recordedDeps_4609_; lean_object* v_messages_4610_; lean_object* v_infoState_4611_; lean_object* v_snapshotTasks_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4637_; 
v___x_4603_ = lean_st_ref_take(v___y_4596_);
v_env_4604_ = lean_ctor_get(v___x_4603_, 0);
v_nextMacroScope_4605_ = lean_ctor_get(v___x_4603_, 1);
v_ngen_4606_ = lean_ctor_get(v___x_4603_, 2);
v_auxDeclNGen_4607_ = lean_ctor_get(v___x_4603_, 3);
v_traceState_4608_ = lean_ctor_get(v___x_4603_, 4);
v_recordedDeps_4609_ = lean_ctor_get(v___x_4603_, 6);
v_messages_4610_ = lean_ctor_get(v___x_4603_, 7);
v_infoState_4611_ = lean_ctor_get(v___x_4603_, 8);
v_snapshotTasks_4612_ = lean_ctor_get(v___x_4603_, 9);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; 
v_unused_4638_ = lean_ctor_get(v___x_4603_, 5);
lean_dec(v_unused_4638_);
v___x_4614_ = v___x_4603_;
v_isShared_4615_ = v_isSharedCheck_4637_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_snapshotTasks_4612_);
lean_inc(v_infoState_4611_);
lean_inc(v_messages_4610_);
lean_inc(v_recordedDeps_4609_);
lean_inc(v_traceState_4608_);
lean_inc(v_auxDeclNGen_4607_);
lean_inc(v_ngen_4606_);
lean_inc(v_nextMacroScope_4605_);
lean_inc(v_env_4604_);
lean_dec(v___x_4603_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4637_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4616_; lean_object* v___x_4618_; 
v___x_4616_ = l_Lean_Environment_setExporting(v_env_4604_, v_isExporting_4597_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 5, v___x_4598_);
lean_ctor_set(v___x_4614_, 0, v___x_4616_);
v___x_4618_ = v___x_4614_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_nextMacroScope_4605_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_ngen_4606_);
lean_ctor_set(v_reuseFailAlloc_4636_, 3, v_auxDeclNGen_4607_);
lean_ctor_set(v_reuseFailAlloc_4636_, 4, v_traceState_4608_);
lean_ctor_set(v_reuseFailAlloc_4636_, 5, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4636_, 6, v_recordedDeps_4609_);
lean_ctor_set(v_reuseFailAlloc_4636_, 7, v_messages_4610_);
lean_ctor_set(v_reuseFailAlloc_4636_, 8, v_infoState_4611_);
lean_ctor_set(v_reuseFailAlloc_4636_, 9, v_snapshotTasks_4612_);
v___x_4618_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v_mctx_4621_; lean_object* v_zetaDeltaFVarIds_4622_; lean_object* v_postponed_4623_; lean_object* v_diag_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4634_; 
v___x_4619_ = lean_st_ref_put(v___y_4596_, v___x_4618_);
v___x_4620_ = lean_st_ref_take(v___y_4599_);
v_mctx_4621_ = lean_ctor_get(v___x_4620_, 0);
v_zetaDeltaFVarIds_4622_ = lean_ctor_get(v___x_4620_, 2);
v_postponed_4623_ = lean_ctor_get(v___x_4620_, 3);
v_diag_4624_ = lean_ctor_get(v___x_4620_, 4);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4634_ == 0)
{
lean_object* v_unused_4635_; 
v_unused_4635_ = lean_ctor_get(v___x_4620_, 1);
lean_dec(v_unused_4635_);
v___x_4626_ = v___x_4620_;
v_isShared_4627_ = v_isSharedCheck_4634_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_diag_4624_);
lean_inc(v_postponed_4623_);
lean_inc(v_zetaDeltaFVarIds_4622_);
lean_inc(v_mctx_4621_);
lean_dec(v___x_4620_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4634_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4628_ = lean_box(0);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 1, v___x_4600_);
v___x_4630_ = v___x_4626_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_mctx_4621_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4633_, 2, v_zetaDeltaFVarIds_4622_);
lean_ctor_set(v_reuseFailAlloc_4633_, 3, v_postponed_4623_);
lean_ctor_set(v_reuseFailAlloc_4633_, 4, v_diag_4624_);
v___x_4630_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = lean_st_ref_put(v___y_4599_, v___x_4630_);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4628_);
return v___x_4632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___lam__0___boxed(lean_object* v___y_4639_, lean_object* v_isExporting_4640_, lean_object* v___x_4641_, lean_object* v___y_4642_, lean_object* v___x_4643_, lean_object* v_a_x3f_4644_, lean_object* v___y_4645_){
_start:
{
uint8_t v_isExporting_boxed_4646_; lean_object* v_res_4647_; 
v_isExporting_boxed_4646_ = lean_unbox(v_isExporting_4640_);
v_res_4647_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___lam__0(v___y_4639_, v_isExporting_boxed_4646_, v___x_4641_, v___y_4642_, v___x_4643_, v_a_x3f_4644_);
lean_dec(v_a_x3f_4644_);
lean_dec(v___y_4642_);
lean_dec(v___y_4639_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg(lean_object* v_x_4648_, uint8_t v_isExporting_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; lean_object* v_env_4658_; lean_object* v___x_4659_; uint8_t v_isModule_4660_; 
v___x_4657_ = lean_st_ref_get(v___y_4655_);
v_env_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc_ref(v_env_4658_);
lean_dec(v___x_4657_);
v___x_4659_ = l_Lean_Environment_header(v_env_4658_);
v_isModule_4660_ = lean_ctor_get_uint8(v___x_4659_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4659_);
if (v_isModule_4660_ == 0)
{
lean_object* v___x_4661_; 
lean_dec_ref(v_env_4658_);
lean_inc(v___y_4655_);
lean_inc_ref(v___y_4654_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
v___x_4661_ = lean_apply_7(v_x_4648_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, lean_box(0));
return v___x_4661_;
}
else
{
uint8_t v_isExporting_4662_; 
v_isExporting_4662_ = lean_ctor_get_uint8(v_env_4658_, sizeof(void*)*13);
lean_dec_ref(v_env_4658_);
if (v_isExporting_4649_ == 0)
{
if (v_isExporting_4662_ == 0)
{
lean_object* v___x_4729_; 
lean_inc(v___y_4655_);
lean_inc_ref(v___y_4654_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
v___x_4729_ = lean_apply_7(v_x_4648_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, lean_box(0));
return v___x_4729_;
}
else
{
goto v___jp_4663_;
}
}
else
{
if (v_isExporting_4662_ == 0)
{
goto v___jp_4663_;
}
else
{
lean_object* v___x_4730_; 
lean_inc(v___y_4655_);
lean_inc_ref(v___y_4654_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
v___x_4730_ = lean_apply_7(v_x_4648_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, lean_box(0));
return v___x_4730_;
}
}
v___jp_4663_:
{
lean_object* v___x_4664_; lean_object* v_env_4665_; lean_object* v_nextMacroScope_4666_; lean_object* v_ngen_4667_; lean_object* v_auxDeclNGen_4668_; lean_object* v_traceState_4669_; lean_object* v_recordedDeps_4670_; lean_object* v_messages_4671_; lean_object* v_infoState_4672_; lean_object* v_snapshotTasks_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4727_; 
v___x_4664_ = lean_st_ref_take(v___y_4655_);
v_env_4665_ = lean_ctor_get(v___x_4664_, 0);
v_nextMacroScope_4666_ = lean_ctor_get(v___x_4664_, 1);
v_ngen_4667_ = lean_ctor_get(v___x_4664_, 2);
v_auxDeclNGen_4668_ = lean_ctor_get(v___x_4664_, 3);
v_traceState_4669_ = lean_ctor_get(v___x_4664_, 4);
v_recordedDeps_4670_ = lean_ctor_get(v___x_4664_, 6);
v_messages_4671_ = lean_ctor_get(v___x_4664_, 7);
v_infoState_4672_ = lean_ctor_get(v___x_4664_, 8);
v_snapshotTasks_4673_ = lean_ctor_get(v___x_4664_, 9);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; 
v_unused_4728_ = lean_ctor_get(v___x_4664_, 5);
lean_dec(v_unused_4728_);
v___x_4675_ = v___x_4664_;
v_isShared_4676_ = v_isSharedCheck_4727_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_snapshotTasks_4673_);
lean_inc(v_infoState_4672_);
lean_inc(v_messages_4671_);
lean_inc(v_recordedDeps_4670_);
lean_inc(v_traceState_4669_);
lean_inc(v_auxDeclNGen_4668_);
lean_inc(v_ngen_4667_);
lean_inc(v_nextMacroScope_4666_);
lean_inc(v_env_4665_);
lean_dec(v___x_4664_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4727_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4680_; 
v___x_4677_ = l_Lean_Environment_setExporting(v_env_4665_, v_isExporting_4649_);
v___x_4678_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 5, v___x_4678_);
lean_ctor_set(v___x_4675_, 0, v___x_4677_);
v___x_4680_ = v___x_4675_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v_nextMacroScope_4666_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_ngen_4667_);
lean_ctor_set(v_reuseFailAlloc_4726_, 3, v_auxDeclNGen_4668_);
lean_ctor_set(v_reuseFailAlloc_4726_, 4, v_traceState_4669_);
lean_ctor_set(v_reuseFailAlloc_4726_, 5, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4726_, 6, v_recordedDeps_4670_);
lean_ctor_set(v_reuseFailAlloc_4726_, 7, v_messages_4671_);
lean_ctor_set(v_reuseFailAlloc_4726_, 8, v_infoState_4672_);
lean_ctor_set(v_reuseFailAlloc_4726_, 9, v_snapshotTasks_4673_);
v___x_4680_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v_mctx_4683_; lean_object* v_zetaDeltaFVarIds_4684_; lean_object* v_postponed_4685_; lean_object* v_diag_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4724_; 
v___x_4681_ = lean_st_ref_put(v___y_4655_, v___x_4680_);
v___x_4682_ = lean_st_ref_take(v___y_4653_);
v_mctx_4683_ = lean_ctor_get(v___x_4682_, 0);
v_zetaDeltaFVarIds_4684_ = lean_ctor_get(v___x_4682_, 2);
v_postponed_4685_ = lean_ctor_get(v___x_4682_, 3);
v_diag_4686_ = lean_ctor_get(v___x_4682_, 4);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; 
v_unused_4725_ = lean_ctor_get(v___x_4682_, 1);
lean_dec(v_unused_4725_);
v___x_4688_ = v___x_4682_;
v_isShared_4689_ = v_isSharedCheck_4724_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_diag_4686_);
lean_inc(v_postponed_4685_);
lean_inc(v_zetaDeltaFVarIds_4684_);
lean_inc(v_mctx_4683_);
lean_dec(v___x_4682_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4724_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4690_; lean_object* v___x_4692_; 
v___x_4690_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__7);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 1, v___x_4690_);
v___x_4692_ = v___x_4688_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_mctx_4683_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v___x_4690_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_zetaDeltaFVarIds_4684_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v_postponed_4685_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v_diag_4686_);
v___x_4692_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
lean_object* v___x_4693_; lean_object* v_r_4694_; 
v___x_4693_ = lean_st_ref_put(v___y_4653_, v___x_4692_);
lean_inc(v___y_4655_);
lean_inc_ref(v___y_4654_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
v_r_4694_ = lean_apply_7(v_x_4648_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, lean_box(0));
if (lean_obj_tag(v_r_4694_) == 0)
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4711_; 
v_a_4695_ = lean_ctor_get(v_r_4694_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v_r_4694_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4697_ = v_r_4694_;
v_isShared_4698_ = v_isSharedCheck_4711_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v_r_4694_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4711_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
lean_inc(v_a_4695_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set_tag(v___x_4697_, 1);
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
lean_object* v___x_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
v___x_4701_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___lam__0(v___y_4655_, v_isExporting_4662_, v___x_4678_, v___y_4653_, v___x_4690_, v___x_4700_);
lean_dec_ref(v___x_4700_);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4708_ == 0)
{
lean_object* v_unused_4709_; 
v_unused_4709_ = lean_ctor_get(v___x_4701_, 0);
lean_dec(v_unused_4709_);
v___x_4703_ = v___x_4701_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_dec(v___x_4701_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 0, v_a_4695_);
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4695_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
v_a_4712_ = lean_ctor_get(v_r_4694_, 0);
lean_inc(v_a_4712_);
lean_dec_ref_known(v_r_4694_, 1);
v___x_4713_ = lean_box(0);
v___x_4714_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___lam__0(v___y_4655_, v_isExporting_4662_, v___x_4678_, v___y_4653_, v___x_4690_, v___x_4713_);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4721_ == 0)
{
lean_object* v_unused_4722_; 
v_unused_4722_ = lean_ctor_get(v___x_4714_, 0);
lean_dec(v_unused_4722_);
v___x_4716_ = v___x_4714_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_dec(v___x_4714_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
lean_ctor_set_tag(v___x_4716_, 1);
lean_ctor_set(v___x_4716_, 0, v_a_4712_);
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4712_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg___boxed(lean_object* v_x_4731_, lean_object* v_isExporting_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
uint8_t v_isExporting_boxed_4740_; lean_object* v_res_4741_; 
v_isExporting_boxed_4740_ = lean_unbox(v_isExporting_4732_);
v_res_4741_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg(v_x_4731_, v_isExporting_boxed_4740_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4744_, lean_object* v_ctorName_4745_, uint8_t v_addHypotheses_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v___f_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___f_4761_; uint8_t v___x_4762_; 
v___f_4754_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4755_ = lean_box(0);
v___x_4756_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4757_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4758_ = 1;
v___x_4759_ = lean_box(v___x_4758_);
v___x_4760_ = lean_box(v_addHypotheses_4746_);
lean_inc(v_ctorName_4745_);
v___f_4761_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4761_, 0, v___x_4756_);
lean_closure_set(v___f_4761_, 1, v___x_4757_);
lean_closure_set(v___f_4761_, 2, v_inductiveTypeName_4744_);
lean_closure_set(v___f_4761_, 3, v___x_4759_);
lean_closure_set(v___f_4761_, 4, v___x_4755_);
lean_closure_set(v___f_4761_, 5, v___f_4754_);
lean_closure_set(v___f_4761_, 6, v_ctorName_4745_);
lean_closure_set(v___f_4761_, 7, v___x_4760_);
v___x_4762_ = l_Lean_isPrivateName(v_ctorName_4745_);
lean_dec(v_ctorName_4745_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; 
v___x_4763_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg(v___f_4761_, v___x_4758_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4763_;
}
else
{
uint8_t v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = 0;
v___x_4765_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg(v___f_4761_, v___x_4764_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4766_, lean_object* v_ctorName_4767_, lean_object* v_addHypotheses_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
uint8_t v_addHypotheses_boxed_4776_; lean_object* v_res_4777_; 
v_addHypotheses_boxed_4776_ = lean_unbox(v_addHypotheses_4768_);
v_res_4777_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4766_, v_ctorName_4767_, v_addHypotheses_boxed_4776_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1(lean_object* v_00_u03b2_4778_){
_start:
{
lean_object* v___x_4779_; 
v___x_4779_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(){
_start:
{
lean_object* v___x_4781_; 
v___x_4781_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v___dummy_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg();
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b2_4784_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__6);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2(lean_object* v_00_u03b1_4786_, lean_object* v_x_4787_, uint8_t v_isExporting_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___redArg(v_x_4787_, v_isExporting_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2___boxed(lean_object* v_00_u03b1_4797_, lean_object* v_x_4798_, lean_object* v_isExporting_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
uint8_t v_isExporting_boxed_4807_; lean_object* v_res_4808_; 
v_isExporting_boxed_4807_ = lean_unbox(v_isExporting_4799_);
v_res_4808_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__2(v_00_u03b1_4797_, v_x_4798_, v_isExporting_boxed_4807_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4809_, lean_object* v_ctorName_4810_, uint8_t v_addHypotheses_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4815_ = lean_box(v_addHypotheses_4811_);
v___x_4816_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4816_, 0, v_inductiveTypeName_4809_);
lean_closure_set(v___x_4816_, 1, v_ctorName_4810_);
lean_closure_set(v___x_4816_, 2, v___x_4815_);
v___x_4817_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4816_, v_a_4812_, v_a_4813_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4847_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4847_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4847_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
if (lean_obj_tag(v_a_4818_) == 0)
{
uint8_t v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4825_; 
v___x_4822_ = 0;
v___x_4823_ = lean_box(v___x_4822_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v___x_4823_);
v___x_4825_ = v___x_4820_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
else
{
lean_object* v_val_4827_; lean_object* v___x_4828_; 
lean_del_object(v___x_4820_);
v_val_4827_ = lean_ctor_get(v_a_4818_, 0);
lean_inc(v_val_4827_);
lean_dec_ref_known(v_a_4818_, 1);
v___x_4828_ = l_Lean_Elab_Command_elabCommand(v_val_4827_, v_a_4812_, v_a_4813_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4837_; 
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4837_ == 0)
{
lean_object* v_unused_4838_; 
v_unused_4838_ = lean_ctor_get(v___x_4828_, 0);
lean_dec(v_unused_4838_);
v___x_4830_ = v___x_4828_;
v_isShared_4831_ = v_isSharedCheck_4837_;
goto v_resetjp_4829_;
}
else
{
lean_dec(v___x_4828_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4837_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
uint8_t v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4832_ = 1;
v___x_4833_ = lean_box(v___x_4832_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 0, v___x_4833_);
v___x_4835_ = v___x_4830_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4833_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4828_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4828_);
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
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
v_a_4848_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4817_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4817_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4856_, lean_object* v_ctorName_4857_, lean_object* v_addHypotheses_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
uint8_t v_addHypotheses_boxed_4862_; lean_object* v_res_4863_; 
v_addHypotheses_boxed_4862_ = lean_unbox(v_addHypotheses_4858_);
v_res_4863_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4856_, v_ctorName_4857_, v_addHypotheses_boxed_4862_, v_a_4859_, v_a_4860_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4867_, uint8_t v_addHypotheses_4868_, lean_object* v_as_x27_4869_, lean_object* v_b_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
if (lean_obj_tag(v_as_x27_4869_) == 0)
{
lean_object* v___x_4874_; 
lean_dec(v_declName_4867_);
v___x_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4874_, 0, v_b_4870_);
return v___x_4874_;
}
else
{
lean_object* v_head_4875_; lean_object* v_tail_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
lean_dec_ref(v_b_4870_);
v_head_4875_ = lean_ctor_get(v_as_x27_4869_, 0);
v_tail_4876_ = lean_ctor_get(v_as_x27_4869_, 1);
v___x_4877_ = lean_box(0);
v___x_4878_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
lean_inc(v_head_4875_);
lean_inc(v_declName_4867_);
v___x_4879_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4867_, v_head_4875_, v_addHypotheses_4868_, v___y_4871_, v___y_4872_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4891_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4891_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4891_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
uint8_t v___x_4884_; 
v___x_4884_ = lean_unbox(v_a_4880_);
if (v___x_4884_ == 0)
{
lean_del_object(v___x_4882_);
lean_dec(v_a_4880_);
v_as_x27_4869_ = v_tail_4876_;
v_b_4870_ = v___x_4878_;
goto _start;
}
else
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4889_; 
lean_dec(v_declName_4867_);
v___x_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4886_, 0, v_a_4880_);
v___x_4887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v___x_4877_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4887_);
v___x_4889_ = v___x_4882_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec(v_declName_4867_);
v_a_4892_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4879_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4879_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4900_, lean_object* v_addHypotheses_4901_, lean_object* v_as_x27_4902_, lean_object* v_b_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
uint8_t v_addHypotheses_boxed_4907_; lean_object* v_res_4908_; 
v_addHypotheses_boxed_4907_ = lean_unbox(v_addHypotheses_4901_);
v_res_4908_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4900_, v_addHypotheses_boxed_4907_, v_as_x27_4902_, v_b_4903_, v___y_4904_, v___y_4905_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v_as_x27_4902_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4909_, lean_object* v_declName_4910_, uint8_t v_addHypotheses_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_ctors_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v_ctors_4915_ = lean_ctor_get(v_a_4909_, 4);
v___x_4916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4917_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4910_, v_addHypotheses_4911_, v_ctors_4915_, v___x_4916_, v___y_4912_, v___y_4913_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4932_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4932_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4932_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_fst_4922_; 
v_fst_4922_ = lean_ctor_get(v_a_4918_, 0);
lean_inc(v_fst_4922_);
lean_dec(v_a_4918_);
if (lean_obj_tag(v_fst_4922_) == 0)
{
uint8_t v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4926_; 
v___x_4923_ = 0;
v___x_4924_ = lean_box(v___x_4923_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4924_);
v___x_4926_ = v___x_4920_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4924_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
else
{
lean_object* v_val_4928_; lean_object* v___x_4930_; 
v_val_4928_ = lean_ctor_get(v_fst_4922_, 0);
lean_inc(v_val_4928_);
lean_dec_ref_known(v_fst_4922_, 1);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v_val_4928_);
v___x_4930_ = v___x_4920_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_val_4928_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4940_; 
v_a_4933_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4935_ = v___x_4917_;
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4917_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4938_; 
if (v_isShared_4936_ == 0)
{
v___x_4938_ = v___x_4935_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_4941_, lean_object* v_declName_4942_, lean_object* v_addHypotheses_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
uint8_t v_addHypotheses_boxed_4947_; lean_object* v_res_4948_; 
v_addHypotheses_boxed_4947_ = lean_unbox(v_addHypotheses_4943_);
v_res_4948_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_4941_, v_declName_4942_, v_addHypotheses_boxed_4947_, v___y_4944_, v___y_4945_);
lean_dec(v___y_4945_);
lean_dec_ref(v___y_4944_);
lean_dec_ref(v_a_4941_);
return v_res_4948_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_spec__1___redArg___closed__0);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4949_);
return v___x_4950_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4951_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4952_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4953_ = lean_unsigned_to_nat(0u);
v___x_4954_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
lean_ctor_set(v___x_4954_, 1, v___x_4953_);
lean_ctor_set(v___x_4954_, 2, v___x_4953_);
lean_ctor_set(v___x_4954_, 3, v___x_4953_);
lean_ctor_set(v___x_4954_, 4, v___x_4952_);
lean_ctor_set(v___x_4954_, 5, v___x_4952_);
lean_ctor_set(v___x_4954_, 6, v___x_4952_);
lean_ctor_set(v___x_4954_, 7, v___x_4952_);
lean_ctor_set(v___x_4954_, 8, v___x_4952_);
lean_ctor_set(v___x_4954_, 9, v___x_4952_);
lean_ctor_set(v___x_4954_, 10, v___x_4952_);
lean_ctor_set(v___x_4954_, 11, v___x_4951_);
return v___x_4954_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4955_ = lean_unsigned_to_nat(32u);
v___x_4956_ = lean_mk_empty_array_with_capacity(v___x_4955_);
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4956_);
return v___x_4957_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
size_t v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4958_ = ((size_t)5ULL);
v___x_4959_ = lean_unsigned_to_nat(0u);
v___x_4960_ = lean_unsigned_to_nat(32u);
v___x_4961_ = lean_mk_empty_array_with_capacity(v___x_4960_);
v___x_4962_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_4963_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
lean_ctor_set(v___x_4963_, 1, v___x_4961_);
lean_ctor_set(v___x_4963_, 2, v___x_4959_);
lean_ctor_set(v___x_4963_, 3, v___x_4959_);
lean_ctor_set_usize(v___x_4963_, 4, v___x_4958_);
return v___x_4963_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4964_ = lean_box(1);
v___x_4965_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_4966_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4966_);
lean_ctor_set(v___x_4967_, 1, v___x_4965_);
lean_ctor_set(v___x_4967_, 2, v___x_4964_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v___x_4971_; lean_object* v_env_4972_; uint8_t v___x_4973_; lean_object* v_env_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v_scopes_4977_; lean_object* v___x_4978_; lean_object* v_opts_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4971_ = lean_st_ref_get(v___y_4969_);
v_env_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc_ref(v_env_4972_);
lean_dec(v___x_4971_);
v___x_4973_ = 0;
v_env_4974_ = l_Lean_Environment_setRecordingDeps(v_env_4972_, v___x_4973_);
v___x_4975_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4976_ = lean_st_ref_get(v___y_4969_);
v_scopes_4977_ = lean_ctor_get(v___x_4976_, 2);
lean_inc(v_scopes_4977_);
lean_dec(v___x_4976_);
v___x_4978_ = l_List_head_x21___redArg(v___x_4975_, v_scopes_4977_);
lean_dec(v_scopes_4977_);
v_opts_4979_ = lean_ctor_get(v___x_4978_, 1);
lean_inc_ref(v_opts_4979_);
lean_dec(v___x_4978_);
v___x_4980_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4981_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_4982_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4982_, 0, v_env_4974_);
lean_ctor_set(v___x_4982_, 1, v___x_4980_);
lean_ctor_set(v___x_4982_, 2, v___x_4981_);
lean_ctor_set(v___x_4982_, 3, v_opts_4979_);
v___x_4983_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
lean_ctor_set(v___x_4983_, 1, v_msgData_4968_);
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_4985_, v___y_4986_);
lean_dec(v___y_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_4989_, lean_object* v_macroStack_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v_scopes_4995_; lean_object* v___x_4996_; lean_object* v_opts_4997_; lean_object* v___x_4998_; uint8_t v___x_4999_; 
v___x_4993_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4994_ = lean_st_ref_get(v___y_4991_);
v_scopes_4995_ = lean_ctor_get(v___x_4994_, 2);
lean_inc(v_scopes_4995_);
lean_dec(v___x_4994_);
v___x_4996_ = l_List_head_x21___redArg(v___x_4993_, v_scopes_4995_);
lean_dec(v_scopes_4995_);
v_opts_4997_ = lean_ctor_get(v___x_4996_, 1);
lean_inc_ref(v_opts_4997_);
lean_dec(v___x_4996_);
v___x_4998_ = l_Lean_Elab_pp_macroStack;
v___x_4999_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_4997_, v___x_4998_);
lean_dec_ref(v_opts_4997_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; 
lean_dec(v_macroStack_4990_);
v___x_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5000_, 0, v_msgData_4989_);
return v___x_5000_;
}
else
{
if (lean_obj_tag(v_macroStack_4990_) == 0)
{
lean_object* v___x_5001_; 
v___x_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5001_, 0, v_msgData_4989_);
return v___x_5001_;
}
else
{
lean_object* v_head_5002_; lean_object* v_after_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5018_; 
v_head_5002_ = lean_ctor_get(v_macroStack_4990_, 0);
lean_inc(v_head_5002_);
v_after_5003_ = lean_ctor_get(v_head_5002_, 1);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_head_5002_);
if (v_isSharedCheck_5018_ == 0)
{
lean_object* v_unused_5019_; 
v_unused_5019_ = lean_ctor_get(v_head_5002_, 0);
lean_dec(v_unused_5019_);
v___x_5005_ = v_head_5002_;
v_isShared_5006_ = v_isSharedCheck_5018_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_after_5003_);
lean_dec(v_head_5002_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5018_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5007_; lean_object* v___x_5009_; 
v___x_5007_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_5006_ == 0)
{
lean_ctor_set_tag(v___x_5005_, 7);
lean_ctor_set(v___x_5005_, 1, v___x_5007_);
lean_ctor_set(v___x_5005_, 0, v_msgData_4989_);
v___x_5009_ = v___x_5005_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_msgData_4989_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v_msgData_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5010_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_5011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5009_);
lean_ctor_set(v___x_5011_, 1, v___x_5010_);
v___x_5012_ = l_Lean_MessageData_ofSyntax(v_after_5003_);
v___x_5013_ = l_Lean_indentD(v___x_5012_);
v_msgData_5014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5014_, 0, v___x_5011_);
lean_ctor_set(v_msgData_5014_, 1, v___x_5013_);
v___x_5015_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_5014_, v_macroStack_4990_);
v___x_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5015_);
return v___x_5016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_5020_, lean_object* v_macroStack_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5020_, v_macroStack_5021_, v___y_5022_);
lean_dec(v___y_5022_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v___x_5029_; 
v___x_5029_ = l_Lean_Elab_Command_getRef___redArg(v___y_5026_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; lean_object* v_macroStack_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v_a_5034_; lean_object* v___x_5035_; lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5044_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref_known(v___x_5029_, 1);
v_macroStack_5031_ = lean_ctor_get(v___y_5026_, 4);
v___x_5032_ = l_Lean_Elab_getBetterRef(v_a_5030_, v_macroStack_5031_);
lean_dec(v_a_5030_);
v___x_5033_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_5025_, v___y_5027_);
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref(v___x_5033_);
lean_inc(v_macroStack_5031_);
v___x_5035_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_5034_, v_macroStack_5031_, v___y_5027_);
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5038_ = v___x_5035_;
v_isShared_5039_ = v_isSharedCheck_5044_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5035_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5044_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5040_; lean_object* v___x_5042_; 
v___x_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5032_);
lean_ctor_set(v___x_5040_, 1, v_a_5036_);
if (v_isShared_5039_ == 0)
{
lean_ctor_set_tag(v___x_5038_, 1);
lean_ctor_set(v___x_5038_, 0, v___x_5040_);
v___x_5042_ = v___x_5038_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_dec_ref(v_msg_5025_);
v_a_5045_ = lean_ctor_get(v___x_5029_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5029_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5029_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v___x_5062_; lean_object* v_env_5063_; lean_object* v___x_5064_; 
v___x_5062_ = lean_st_ref_get(v___y_5060_);
v_env_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc_ref(v_env_5063_);
lean_dec(v___x_5062_);
lean_inc(v_constName_5058_);
v___x_5064_ = l_Lean_isInductiveCore_x3f(v_env_5063_, v_constName_5058_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v___x_5065_; uint8_t v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5065_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5066_ = 0;
v___x_5067_ = l_Lean_MessageData_ofConstName(v_constName_5058_, v___x_5066_);
v___x_5068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5065_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
v___x_5069_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5068_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5070_, v___y_5059_, v___y_5060_);
return v___x_5071_;
}
else
{
lean_object* v_val_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_dec(v_constName_5058_);
v_val_5072_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5064_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_val_5072_);
lean_dec(v___x_5064_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
lean_ctor_set_tag(v___x_5074_, 0);
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_val_5072_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5080_, v___y_5081_, v___y_5082_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
return v_res_5084_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5086_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5087_ = l_Lean_stringToMessageData(v___x_5086_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v___x_5095_; 
lean_inc(v_declName_5088_);
v___x_5095_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5088_, v___y_5089_, v___y_5090_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v_a_5096_; uint8_t v___x_5097_; lean_object* v___x_5098_; 
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc(v_a_5096_);
lean_dec_ref_known(v___x_5095_, 1);
v___x_5097_ = 0;
lean_inc(v_declName_5088_);
v___x_5098_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5096_, v_declName_5088_, v___x_5097_, v___y_5089_, v___y_5090_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; uint8_t v___x_5100_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
v___x_5100_ = lean_unbox(v_a_5099_);
lean_dec(v_a_5099_);
if (v___x_5100_ == 0)
{
uint8_t v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = 1;
lean_inc(v_declName_5088_);
v___x_5102_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5096_, v_declName_5088_, v___x_5101_, v___y_5089_, v___y_5090_);
lean_dec(v_a_5096_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; uint8_t v___x_5104_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___x_5102_, 1);
v___x_5104_ = lean_unbox(v_a_5103_);
lean_dec(v_a_5103_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5105_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5106_ = l_Lean_MessageData_ofConstName(v_declName_5088_, v___x_5097_);
v___x_5107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5105_);
lean_ctor_set(v___x_5107_, 1, v___x_5106_);
v___x_5108_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5107_);
lean_ctor_set(v___x_5109_, 1, v___x_5108_);
v___x_5110_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5109_, v___y_5089_, v___y_5090_);
return v___x_5110_;
}
else
{
lean_dec(v_declName_5088_);
goto v___jp_5092_;
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec(v_declName_5088_);
v_a_5111_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5102_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5102_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_dec(v_a_5096_);
lean_dec(v_declName_5088_);
goto v___jp_5092_;
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec(v_a_5096_);
lean_dec(v_declName_5088_);
v_a_5119_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5098_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5098_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
lean_dec(v_declName_5088_);
v_a_5127_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5095_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5095_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
v___jp_5092_:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_box(0);
v___x_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
return v___x_5094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5135_, v___y_5136_, v___y_5137_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
lean_object* v___f_5144_; lean_object* v___x_5145_; 
lean_inc(v_declName_5140_);
v___f_5144_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5144_, 0, v_declName_5140_);
v___x_5145_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5140_, v___f_5144_, v_a_5141_, v_a_5142_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5146_, v_a_5147_, v_a_5148_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5151_, uint8_t v_addHypotheses_5152_, lean_object* v_as_5153_, lean_object* v_as_x27_5154_, lean_object* v_b_5155_, lean_object* v_a_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5151_, v_addHypotheses_5152_, v_as_x27_5154_, v_b_5155_, v___y_5157_, v___y_5158_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5161_, lean_object* v_addHypotheses_5162_, lean_object* v_as_5163_, lean_object* v_as_x27_5164_, lean_object* v_b_5165_, lean_object* v_a_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_){
_start:
{
uint8_t v_addHypotheses_boxed_5170_; lean_object* v_res_5171_; 
v_addHypotheses_boxed_5170_ = lean_unbox(v_addHypotheses_5162_);
v_res_5171_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5161_, v_addHypotheses_boxed_5170_, v_as_5163_, v_as_x27_5164_, v_b_5165_, v_a_5166_, v___y_5167_, v___y_5168_);
lean_dec(v___y_5168_);
lean_dec_ref(v___y_5167_);
lean_dec(v_as_x27_5164_);
lean_dec(v_as_5163_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5172_, v___y_5174_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5177_, v___y_5178_, v___y_5179_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5182_, lean_object* v_msg_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5183_, v___y_5184_, v___y_5185_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5188_, lean_object* v_msg_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5188_, v_msg_5189_, v___y_5190_, v___y_5191_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5194_, lean_object* v_macroStack_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5194_, v_macroStack_5195_, v___y_5197_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5200_, lean_object* v_macroStack_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5200_, v_macroStack_5201_, v___y_5202_, v___y_5203_);
lean_dec(v___y_5203_);
lean_dec_ref(v___y_5202_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v___x_5209_; lean_object* v_env_5210_; uint8_t v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5209_ = lean_st_ref_get(v___y_5207_);
v_env_5210_ = lean_ctor_get(v___x_5209_, 0);
lean_inc_ref(v_env_5210_);
lean_dec(v___x_5209_);
v___x_5211_ = l_Lean_isInductiveCore(v_env_5210_, v_declName_5206_);
v___x_5212_ = lean_box(v___x_5211_);
v___x_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5213_, 0, v___x_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5214_, v___y_5215_);
lean_dec(v___y_5215_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
lean_object* v___x_5222_; 
v___x_5222_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5218_, v___y_5220_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5223_, v___y_5224_, v___y_5225_);
lean_dec(v___y_5225_);
lean_dec_ref(v___y_5224_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
if (v_____do__lift_5228_ == 0)
{
uint8_t v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
v___x_5232_ = 1;
v___x_5233_ = lean_box(v___x_5232_);
v___x_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5233_);
return v___x_5234_;
}
else
{
uint8_t v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v___x_5235_ = 0;
v___x_5236_ = lean_box(v___x_5235_);
v___x_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5236_);
return v___x_5237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
uint8_t v_____do__lift_1604__boxed_5242_; lean_object* v_res_5243_; 
v_____do__lift_1604__boxed_5242_ = lean_unbox(v_____do__lift_5238_);
v_res_5243_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1604__boxed_5242_, v___y_5239_, v___y_5240_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5244_, size_t v_i_5245_, size_t v_stop_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
uint8_t v___x_5250_; 
v___x_5250_ = lean_usize_dec_eq(v_i_5245_, v_stop_5246_);
if (v___x_5250_ == 0)
{
uint8_t v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
v___x_5251_ = 1;
v___x_5252_ = lean_array_uget_borrowed(v_as_5244_, v_i_5245_);
lean_inc(v___x_5252_);
v___x_5253_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5252_, v___y_5248_);
if (lean_obj_tag(v___x_5253_) == 0)
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5266_; 
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5256_ = v___x_5253_;
v_isShared_5257_ = v_isSharedCheck_5266_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5266_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
uint8_t v___x_5258_; 
v___x_5258_ = lean_unbox(v_a_5254_);
lean_dec(v_a_5254_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; lean_object* v___x_5261_; 
v___x_5259_ = lean_box(v___x_5251_);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 0, v___x_5259_);
v___x_5261_ = v___x_5256_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5259_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
else
{
size_t v___x_5263_; size_t v___x_5264_; 
lean_del_object(v___x_5256_);
v___x_5263_ = ((size_t)1ULL);
v___x_5264_ = lean_usize_add(v_i_5245_, v___x_5263_);
v_i_5245_ = v___x_5264_;
goto _start;
}
}
}
else
{
return v___x_5253_;
}
}
else
{
uint8_t v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5267_ = 0;
v___x_5268_ = lean_box(v___x_5267_);
v___x_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5268_);
return v___x_5269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5270_, lean_object* v_i_5271_, lean_object* v_stop_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
size_t v_i_boxed_5276_; size_t v_stop_boxed_5277_; lean_object* v_res_5278_; 
v_i_boxed_5276_ = lean_unbox_usize(v_i_5271_);
lean_dec(v_i_5271_);
v_stop_boxed_5277_ = lean_unbox_usize(v_stop_5272_);
lean_dec(v_stop_5272_);
v_res_5278_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5270_, v_i_boxed_5276_, v_stop_boxed_5277_, v___y_5273_, v___y_5274_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec_ref(v_as_5270_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5279_, size_t v_i_5280_, size_t v_stop_5281_, lean_object* v_b_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
uint8_t v___x_5286_; 
v___x_5286_ = lean_usize_dec_eq(v_i_5280_, v_stop_5281_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = lean_array_uget_borrowed(v_as_5279_, v_i_5280_);
lean_inc(v___x_5287_);
v___x_5288_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5287_, v___y_5283_, v___y_5284_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; size_t v___x_5290_; size_t v___x_5291_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
lean_inc(v_a_5289_);
lean_dec_ref_known(v___x_5288_, 1);
v___x_5290_ = ((size_t)1ULL);
v___x_5291_ = lean_usize_add(v_i_5280_, v___x_5290_);
v_i_5280_ = v___x_5291_;
v_b_5282_ = v_a_5289_;
goto _start;
}
else
{
return v___x_5288_;
}
}
else
{
lean_object* v___x_5293_; 
v___x_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5293_, 0, v_b_5282_);
return v___x_5293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5294_, lean_object* v_i_5295_, lean_object* v_stop_5296_, lean_object* v_b_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
size_t v_i_boxed_5301_; size_t v_stop_boxed_5302_; lean_object* v_res_5303_; 
v_i_boxed_5301_ = lean_unbox_usize(v_i_5295_);
lean_dec(v_i_5295_);
v_stop_boxed_5302_ = lean_unbox_usize(v_stop_5296_);
lean_dec(v_stop_5296_);
v_res_5303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5294_, v_i_boxed_5301_, v_stop_boxed_5302_, v_b_5297_, v___y_5298_, v___y_5299_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec_ref(v_as_5294_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_){
_start:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___y_5337_; uint8_t v___x_5340_; 
v___x_5308_ = lean_unsigned_to_nat(0u);
v___x_5309_ = lean_array_get_size(v_declNames_5304_);
v___x_5340_ = lean_nat_dec_lt(v___x_5308_, v___x_5309_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; 
v___x_5341_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5340_, v_a_5305_, v_a_5306_);
v___y_5337_ = v___x_5341_;
goto v___jp_5336_;
}
else
{
if (v___x_5340_ == 0)
{
goto v___jp_5310_;
}
else
{
size_t v___x_5342_; size_t v___x_5343_; lean_object* v___x_5344_; 
v___x_5342_ = ((size_t)0ULL);
v___x_5343_ = lean_usize_of_nat(v___x_5309_);
v___x_5344_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5304_, v___x_5342_, v___x_5343_, v_a_5305_, v_a_5306_);
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_a_5345_; uint8_t v___x_5346_; lean_object* v___x_5347_; 
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
lean_inc(v_a_5345_);
lean_dec_ref_known(v___x_5344_, 1);
v___x_5346_ = lean_unbox(v_a_5345_);
lean_dec(v_a_5345_);
v___x_5347_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5346_, v_a_5305_, v_a_5306_);
v___y_5337_ = v___x_5347_;
goto v___jp_5336_;
}
else
{
return v___x_5344_;
}
}
}
v___jp_5310_:
{
uint8_t v___x_5311_; uint8_t v___x_5312_; 
v___x_5311_ = 1;
v___x_5312_ = lean_nat_dec_lt(v___x_5308_, v___x_5309_);
if (v___x_5312_ == 0)
{
lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5313_ = lean_box(v___x_5311_);
v___x_5314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5313_);
return v___x_5314_;
}
else
{
lean_object* v___x_5315_; size_t v___x_5316_; size_t v___x_5317_; lean_object* v___x_5318_; 
v___x_5315_ = lean_box(0);
v___x_5316_ = ((size_t)0ULL);
v___x_5317_ = lean_usize_of_nat(v___x_5309_);
v___x_5318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5304_, v___x_5316_, v___x_5317_, v___x_5315_, v_a_5305_, v_a_5306_);
if (lean_obj_tag(v___x_5318_) == 0)
{
lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5326_; 
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5326_ == 0)
{
lean_object* v_unused_5327_; 
v_unused_5327_ = lean_ctor_get(v___x_5318_, 0);
lean_dec(v_unused_5327_);
v___x_5320_ = v___x_5318_;
v_isShared_5321_ = v_isSharedCheck_5326_;
goto v_resetjp_5319_;
}
else
{
lean_dec(v___x_5318_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5326_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5322_; lean_object* v___x_5324_; 
v___x_5322_ = lean_box(v___x_5311_);
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v___x_5322_);
v___x_5324_ = v___x_5320_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
else
{
lean_object* v_a_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5335_; 
v_a_5328_ = lean_ctor_get(v___x_5318_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5330_ = v___x_5318_;
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_a_5328_);
lean_dec(v___x_5318_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5333_; 
if (v_isShared_5331_ == 0)
{
v___x_5333_ = v___x_5330_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5328_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
}
}
v___jp_5336_:
{
lean_object* v_a_5338_; uint8_t v___x_5339_; 
v_a_5338_ = lean_ctor_get(v___y_5337_, 0);
v___x_5339_ = lean_unbox(v_a_5338_);
if (v___x_5339_ == 0)
{
return v___y_5337_;
}
else
{
lean_dec_ref(v___y_5337_);
goto v___jp_5310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5348_, v_a_5349_, v_a_5350_);
lean_dec(v_a_5350_);
lean_dec_ref(v_a_5349_);
lean_dec_ref(v_declNames_5348_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5417_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5418_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5419_ = l_Lean_Elab_registerDerivingHandler(v___x_5417_, v___x_5418_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v___x_5420_; uint8_t v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
lean_dec_ref_known(v___x_5419_, 1);
v___x_5420_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5421_ = 0;
v___x_5422_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5423_ = l_Lean_registerTraceClass(v___x_5420_, v___x_5421_, v___x_5422_);
return v___x_5423_;
}
else
{
return v___x_5419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5425_;
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
