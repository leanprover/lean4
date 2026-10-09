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
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "default value contains metavariables"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cannot unify"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "\nand type of constructor"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "structInstDefault"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value),LEAN_SCALAR_PTR_LITERAL(45, 130, 215, 216, 160, 223, 59, 11)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "struct_inst_default%"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v_b_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
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
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_11_;
v_res_11_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0(v_k_1_, v___y_2_, v___y_3_, v_b_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v_b_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0(v_k_12_, v___y_13_, v___y_14_, v_b_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_21_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(lean_object* v_name_22_, uint8_t v_bi_23_, lean_object* v_type_24_, lean_object* v_k_25_, uint8_t v_kind_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_34_, 0, v_k_25_);
lean_closure_set(v___f_34_, 1, v___y_27_);
lean_closure_set(v___f_34_, 2, v___y_28_);
v___x_35_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_22_, v_bi_23_, v_type_24_, v___f_34_, v_kind_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_35_) == 0)
{
return v___x_35_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_22_ = stack[0].m_obj;
uint8_t v_bi_23_ = stack[1].m_num;
lean_object* v_type_24_ = stack[2].m_obj;
lean_object* v_k_25_ = stack[3].m_obj;
uint8_t v_kind_26_ = stack[4].m_num;
lean_object* v___y_27_ = stack[5].m_obj;
lean_object* v___y_28_ = stack[6].m_obj;
lean_object* v___y_29_ = stack[7].m_obj;
lean_object* v___y_30_ = stack[8].m_obj;
lean_object* v___y_31_ = stack[9].m_obj;
lean_object* v___y_32_ = stack[10].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_name_22_, v_bi_23_, v_type_24_, v_k_25_, v_kind_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg___boxed(lean_object* v_name_45_, lean_object* v_bi_46_, lean_object* v_type_47_, lean_object* v_k_48_, lean_object* v_kind_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_bi_boxed_57_; uint8_t v_kind_boxed_58_; lean_object* v_res_59_; 
v_bi_boxed_57_ = lean_unbox(v_bi_46_);
v_kind_boxed_58_ = lean_unbox(v_kind_49_);
v_res_59_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_name_45_, v_bi_boxed_57_, v_type_47_, v_k_48_, v_kind_boxed_58_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_59_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1(lean_object* v_00_u03b1_60_, lean_object* v_name_61_, uint8_t v_bi_62_, lean_object* v_type_63_, lean_object* v_k_64_, uint8_t v_kind_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_name_61_, v_bi_62_, v_type_63_, v_k_64_, v_kind_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_61_ = stack[1].m_obj;
uint8_t v_bi_62_ = stack[2].m_num;
lean_object* v_type_63_ = stack[3].m_obj;
lean_object* v_k_64_ = stack[4].m_obj;
uint8_t v_kind_65_ = stack[5].m_num;
lean_object* v___y_66_ = stack[6].m_obj;
lean_object* v___y_67_ = stack[7].m_obj;
lean_object* v___y_68_ = stack[8].m_obj;
lean_object* v___y_69_ = stack[9].m_obj;
lean_object* v___y_70_ = stack[10].m_obj;
lean_object* v___y_71_ = stack[11].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1(lean_box(0), v_name_61_, v_bi_62_, v_type_63_, v_k_64_, v_kind_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___boxed(lean_object* v_00_u03b1_75_, lean_object* v_name_76_, lean_object* v_bi_77_, lean_object* v_type_78_, lean_object* v_k_79_, lean_object* v_kind_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
uint8_t v_bi_boxed_88_; uint8_t v_kind_boxed_89_; lean_object* v_res_90_; 
v_bi_boxed_88_ = lean_unbox(v_bi_77_);
v_kind_boxed_89_ = lean_unbox(v_kind_80_);
v_res_90_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1(v_00_u03b1_75_, v_name_76_, v_bi_boxed_88_, v_type_78_, v_k_79_, v_kind_boxed_89_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_90_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; lean_object* v_env_98_; uint8_t v___x_99_; lean_object* v_env_100_; lean_object* v___x_101_; lean_object* v_toCold_102_; lean_object* v_mctx_103_; lean_object* v_lctx_104_; lean_object* v_options_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_97_ = lean_st_ref_get(v___y_95_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_env_98_);
lean_dec(v___x_97_);
v___x_99_ = 0;
v_env_100_ = l_Lean_Environment_setRecordingDeps(v_env_98_, v___x_99_);
v___x_101_ = lean_st_ref_get(v___y_93_);
v_toCold_102_ = lean_ctor_get(v___y_94_, 0);
v_mctx_103_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_mctx_103_);
lean_dec(v___x_101_);
v_lctx_104_ = lean_ctor_get(v___y_92_, 2);
v_options_105_ = lean_ctor_get(v_toCold_102_, 2);
lean_inc_ref(v_options_105_);
lean_inc_ref(v_lctx_104_);
v___x_106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_106_, 0, v_env_100_);
lean_ctor_set(v___x_106_, 1, v_mctx_103_);
lean_ctor_set(v___x_106_, 2, v_lctx_104_);
lean_ctor_set(v___x_106_, 3, v_options_105_);
v___x_107_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_msgData_91_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_91_ = stack[0].m_obj;
lean_object* v___y_92_ = stack[1].m_obj;
lean_object* v___y_93_ = stack[2].m_obj;
lean_object* v___y_94_ = stack[3].m_obj;
lean_object* v___y_95_ = stack[4].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msgData_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0___boxed(lean_object* v_msgData_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msgData_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_116_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_117_; double v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_float_of_nat(v___x_117_);
return v___x_118_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(lean_object* v_cls_122_, lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_176_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 2);
v___x_130_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_176_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_176_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_176_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v_traceState_136_; lean_object* v_env_137_; lean_object* v_nextMacroScope_138_; lean_object* v_ngen_139_; lean_object* v_auxDeclNGen_140_; lean_object* v_cache_141_; lean_object* v_recordedDeps_142_; lean_object* v_messages_143_; lean_object* v_infoState_144_; lean_object* v_snapshotTasks_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_175_; 
v___x_135_ = lean_st_ref_take(v___y_127_);
v_traceState_136_ = lean_ctor_get(v___x_135_, 4);
v_env_137_ = lean_ctor_get(v___x_135_, 0);
v_nextMacroScope_138_ = lean_ctor_get(v___x_135_, 1);
v_ngen_139_ = lean_ctor_get(v___x_135_, 2);
v_auxDeclNGen_140_ = lean_ctor_get(v___x_135_, 3);
v_cache_141_ = lean_ctor_get(v___x_135_, 5);
v_recordedDeps_142_ = lean_ctor_get(v___x_135_, 6);
v_messages_143_ = lean_ctor_get(v___x_135_, 7);
v_infoState_144_ = lean_ctor_get(v___x_135_, 8);
v_snapshotTasks_145_ = lean_ctor_get(v___x_135_, 9);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_175_ == 0)
{
v___x_147_ = v___x_135_;
v_isShared_148_ = v_isSharedCheck_175_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_snapshotTasks_145_);
lean_inc(v_infoState_144_);
lean_inc(v_messages_143_);
lean_inc(v_recordedDeps_142_);
lean_inc(v_cache_141_);
lean_inc(v_traceState_136_);
lean_inc(v_auxDeclNGen_140_);
lean_inc(v_ngen_139_);
lean_inc(v_nextMacroScope_138_);
lean_inc(v_env_137_);
lean_dec(v___x_135_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_175_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint64_t v_tid_149_; lean_object* v_traces_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_174_; 
v_tid_149_ = lean_ctor_get_uint64(v_traceState_136_, sizeof(void*)*1);
v_traces_150_ = lean_ctor_get(v_traceState_136_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_traceState_136_);
if (v_isSharedCheck_174_ == 0)
{
v___x_152_ = v_traceState_136_;
v_isShared_153_ = v_isSharedCheck_174_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_traces_150_);
lean_dec(v_traceState_136_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_174_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; double v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_box(0);
v___x_156_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
v___x_157_ = 0;
v___x_158_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_159_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_159_, 0, v_cls_122_);
lean_ctor_set(v___x_159_, 1, v___x_155_);
lean_ctor_set(v___x_159_, 2, v___x_158_);
lean_ctor_set_float(v___x_159_, sizeof(void*)*3, v___x_156_);
lean_ctor_set_float(v___x_159_, sizeof(void*)*3 + 8, v___x_156_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*3 + 16, v___x_157_);
v___x_160_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__2));
v___x_161_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v_a_131_);
lean_ctor_set(v___x_161_, 2, v___x_160_);
lean_inc(v_ref_129_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v_ref_129_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = l_Lean_PersistentArray_push___redArg(v_traces_150_, v___x_162_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_163_);
v___x_165_ = v___x_152_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_163_);
lean_ctor_set_uint64(v_reuseFailAlloc_173_, sizeof(void*)*1, v_tid_149_);
v___x_165_ = v_reuseFailAlloc_173_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 4, v___x_165_);
v___x_167_ = v___x_147_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_env_137_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_nextMacroScope_138_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_ngen_139_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_auxDeclNGen_140_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_172_, 5, v_cache_141_);
lean_ctor_set(v_reuseFailAlloc_172_, 6, v_recordedDeps_142_);
lean_ctor_set(v_reuseFailAlloc_172_, 7, v_messages_143_);
lean_ctor_set(v_reuseFailAlloc_172_, 8, v_infoState_144_);
lean_ctor_set(v_reuseFailAlloc_172_, 9, v_snapshotTasks_145_);
v___x_167_ = v_reuseFailAlloc_172_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_st_ref_put(v___y_127_, v___x_167_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_154_);
v___x_170_ = v___x_133_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_154_);
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
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_122_ = stack[0].m_obj;
lean_object* v_msg_123_ = stack[1].m_obj;
lean_object* v___y_124_ = stack[2].m_obj;
lean_object* v___y_125_ = stack[3].m_obj;
lean_object* v___y_126_ = stack[4].m_obj;
lean_object* v___y_127_ = stack[5].m_obj;
lean_object* v_res_177_;
v_res_177_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_122_, v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___boxed(lean_object* v_cls_178_, lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_178_, v_msg_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_185_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
v___x_198_ = l_Lean_Name_append(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__7));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed(lean_object* v_a_205_, lean_object* v___x_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_k_209_, lean_object* v_tail_210_, lean_object* v_a_211_, lean_object* v_inst_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(v_a_205_, v___x_206_, v_a_207_, v_a_208_, v_k_209_, v_tail_210_, v_a_211_, v_inst_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___x_206_);
return v_res_220_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(lean_object* v_k_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
if (lean_obj_tag(v_a_225_) == 0)
{
lean_object* v___x_236_; 
lean_dec(v_a_226_);
lean_inc(v_a_234_);
lean_inc_ref(v_a_233_);
lean_inc(v_a_232_);
lean_inc_ref(v_a_231_);
lean_inc(v_a_230_);
lean_inc_ref(v_a_229_);
v___x_236_ = lean_apply_9(v_k_224_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, lean_box(0));
return v___x_236_;
}
else
{
lean_object* v_head_237_; lean_object* v_tail_238_; lean_object* v___y_240_; uint8_t v___y_241_; lean_object* v___y_246_; lean_object* v_a_247_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_head_237_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_head_237_);
v_tail_238_ = lean_ctor_get(v_a_225_, 1);
lean_inc(v_tail_238_);
lean_dec_ref_known(v_a_225_, 2);
v___x_250_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_mk_empty_array_with_capacity(v___x_251_);
v___x_253_ = lean_array_push(v___x_252_, v_head_237_);
v___x_254_ = l_Lean_Meta_mkAppM(v___x_250_, v___x_253_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___f_256_; uint8_t v___x_257_; lean_object* v___x_258_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_n(v_a_255_, 3);
lean_dec_ref_known(v___x_254_, 1);
lean_inc(v_tail_238_);
lean_inc_ref(v_k_224_);
lean_inc(v_a_228_);
lean_inc_ref(v_a_227_);
lean_inc(v_a_226_);
v___f_256_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed), 15, 7);
lean_closure_set(v___f_256_, 0, v_a_226_);
lean_closure_set(v___f_256_, 1, v___x_251_);
lean_closure_set(v___f_256_, 2, v_a_227_);
lean_closure_set(v___f_256_, 3, v_a_228_);
lean_closure_set(v___f_256_, 4, v_k_224_);
lean_closure_set(v___f_256_, 5, v_tail_238_);
lean_closure_set(v___f_256_, 6, v_a_255_);
v___x_257_ = 0;
v___x_258_ = l_Lean_Meta_check(v_a_255_, v___x_257_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3));
v___x_260_ = l_Lean_Core_mkFreshUserName(v___x_259_, v_a_233_, v_a_234_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; uint8_t v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = 3;
v___x_263_ = 0;
v___x_264_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_a_261_, v___x_262_, v_a_255_, v___f_256_, v___x_263_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_dec(v_tail_238_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_k_224_);
return v___x_264_;
}
else
{
lean_object* v_a_265_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
v___y_246_ = v___x_264_;
v_a_247_ = v_a_265_;
goto v___jp_245_;
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v___f_256_);
lean_dec(v_a_255_);
v_a_266_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_260_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_260_);
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
v___y_246_ = v___x_271_;
v_a_247_ = v_a_266_;
goto v___jp_245_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v___f_256_);
lean_dec(v_a_255_);
v_a_274_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_258_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_258_);
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
v___y_246_ = v___x_279_;
v_a_247_ = v_a_274_;
goto v___jp_245_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_254_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_254_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
lean_inc(v_a_282_);
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
v___y_246_ = v___x_287_;
v_a_247_ = v_a_282_;
goto v___jp_245_;
}
}
}
v___jp_239_:
{
if (v___y_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v___y_240_);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_a_226_, v___x_242_);
lean_dec(v_a_226_);
v_a_225_ = v_tail_238_;
v_a_226_ = v___x_243_;
goto _start;
}
else
{
lean_dec(v_tail_238_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_k_224_);
return v___y_240_;
}
}
v___jp_245_:
{
uint8_t v___x_248_; 
v___x_248_ = l_Lean_Exception_isInterrupt(v_a_247_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Exception_isRuntime(v_a_247_);
v___y_240_ = v___y_246_;
v___y_241_ = v___x_249_;
goto v___jp_239_;
}
else
{
lean_dec_ref(v_a_247_);
v___y_240_ = v___y_246_;
v___y_241_ = v___x_248_;
goto v___jp_239_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_224_ = stack[0].m_obj;
lean_object* v_a_225_ = stack[1].m_obj;
lean_object* v_a_226_ = stack[2].m_obj;
lean_object* v_a_227_ = stack[3].m_obj;
lean_object* v_a_228_ = stack[4].m_obj;
lean_object* v_a_229_ = stack[5].m_obj;
lean_object* v_a_230_ = stack[6].m_obj;
lean_object* v_a_231_ = stack[7].m_obj;
lean_object* v_a_232_ = stack[8].m_obj;
lean_object* v_a_233_ = stack[9].m_obj;
lean_object* v_a_234_ = stack[10].m_obj;
lean_object* v_res_290_;
v_res_290_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
stack->m_obj
 = v_res_290_;
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(lean_object* v_a_291_, lean_object* v___x_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_k_295_, lean_object* v_tail_296_, lean_object* v_a_297_, lean_object* v_inst_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v_toCold_318_; lean_object* v_options_319_; uint8_t v_hasTrace_320_; 
v_toCold_318_ = lean_ctor_get(v___y_303_, 0);
v_options_319_ = lean_ctor_get(v_toCold_318_, 2);
v_hasTrace_320_ = lean_ctor_get_uint8(v_options_319_, sizeof(void*)*1);
if (v_hasTrace_320_ == 0)
{
lean_dec_ref(v_a_297_);
v___y_307_ = v___y_299_;
v___y_308_ = v___y_300_;
v___y_309_ = v___y_301_;
v___y_310_ = v___y_302_;
v___y_311_ = v___y_303_;
v___y_312_ = v___y_304_;
goto v___jp_306_;
}
else
{
lean_object* v_inheritedTraceOptions_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_inheritedTraceOptions_321_ = lean_ctor_get(v_toCold_318_, 11);
v___x_322_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_323_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_324_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_321_, v_options_319_, v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v_a_297_);
v___y_307_ = v___y_299_;
v___y_308_ = v___y_300_;
v___y_309_ = v___y_301_;
v___y_310_ = v___y_302_;
v___y_311_ = v___y_303_;
v___y_312_ = v___y_304_;
goto v___jp_306_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8);
v___x_326_ = l_Lean_MessageData_ofExpr(v_a_297_);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_322_, v___x_327_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_dec_ref_known(v___x_328_, 1);
v___y_307_ = v___y_299_;
v___y_308_ = v___y_300_;
v___y_309_ = v___y_301_;
v___y_310_ = v___y_302_;
v___y_311_ = v___y_303_;
v___y_312_ = v___y_304_;
goto v___jp_306_;
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v_inst_298_);
lean_dec(v_tail_296_);
lean_dec_ref(v_k_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_291_);
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
v___jp_306_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_313_ = lean_nat_add(v_a_291_, v___x_292_);
lean_inc_ref(v_inst_298_);
v___x_314_ = lean_array_push(v_a_293_, v_inst_298_);
v___x_315_ = l_Lean_Expr_fvarId_x21(v_inst_298_);
lean_dec_ref(v_inst_298_);
v___x_316_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_315_, v_a_291_, v_a_294_);
v___x_317_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_295_, v_tail_296_, v___x_313_, v___x_314_, v___x_316_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
return v___x_317_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_291_ = stack[0].m_obj;
lean_object* v___x_292_ = stack[1].m_obj;
lean_object* v_a_293_ = stack[2].m_obj;
lean_object* v_a_294_ = stack[3].m_obj;
lean_object* v_k_295_ = stack[4].m_obj;
lean_object* v_tail_296_ = stack[5].m_obj;
lean_object* v_a_297_ = stack[6].m_obj;
lean_object* v_inst_298_ = stack[7].m_obj;
lean_object* v___y_299_ = stack[8].m_obj;
lean_object* v___y_300_ = stack[9].m_obj;
lean_object* v___y_301_ = stack[10].m_obj;
lean_object* v___y_302_ = stack[11].m_obj;
lean_object* v___y_303_ = stack[12].m_obj;
lean_object* v___y_304_ = stack[13].m_obj;
lean_object* v_res_337_;
v_res_337_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(v_a_291_, v___x_292_, v_a_293_, v_a_294_, v_k_295_, v_tail_296_, v_a_297_, v_inst_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___boxed(lean_object* v_k_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_350_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(lean_object* v_00_u03b1_351_, lean_object* v_k_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
return v___x_364_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_352_ = stack[1].m_obj;
lean_object* v_a_353_ = stack[2].m_obj;
lean_object* v_a_354_ = stack[3].m_obj;
lean_object* v_a_355_ = stack[4].m_obj;
lean_object* v_a_356_ = stack[5].m_obj;
lean_object* v_a_357_ = stack[6].m_obj;
lean_object* v_a_358_ = stack[7].m_obj;
lean_object* v_a_359_ = stack[8].m_obj;
lean_object* v_a_360_ = stack[9].m_obj;
lean_object* v_a_361_ = stack[10].m_obj;
lean_object* v_a_362_ = stack[11].m_obj;
lean_object* v_res_365_;
v_res_365_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(lean_box(0), v_k_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___boxed(lean_object* v_00_u03b1_366_, lean_object* v_k_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(v_00_u03b1_366_, v_k_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_379_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(lean_object* v_cls_380_, lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_380_, v_msg_381_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_380_ = stack[0].m_obj;
lean_object* v_msg_381_ = stack[1].m_obj;
lean_object* v___y_382_ = stack[2].m_obj;
lean_object* v___y_383_ = stack[3].m_obj;
lean_object* v___y_384_ = stack[4].m_obj;
lean_object* v___y_385_ = stack[5].m_obj;
lean_object* v___y_386_ = stack[6].m_obj;
lean_object* v___y_387_ = stack[7].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(v_cls_380_, v_msg_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___boxed(lean_object* v_cls_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(v_cls_391_, v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_400_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(uint8_t v_addHypotheses_403_, lean_object* v_xs_404_, lean_object* v_k_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
if (v_addHypotheses_403_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v_xs_404_);
v___x_413_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_414_ = lean_box(1);
lean_inc(v_a_411_);
lean_inc_ref(v_a_410_);
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
lean_inc(v_a_407_);
lean_inc_ref(v_a_406_);
v___x_415_ = lean_apply_9(v_k_405_, v___x_413_, v___x_414_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, lean_box(0));
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_416_ = lean_array_to_list(v_xs_404_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_419_ = lean_box(1);
v___x_420_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_405_, v___x_416_, v___x_417_, v___x_418_, v___x_419_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v___x_420_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_addHypotheses_403_ = stack[0].m_num;
lean_object* v_xs_404_ = stack[1].m_obj;
lean_object* v_k_405_ = stack[2].m_obj;
lean_object* v_a_406_ = stack[3].m_obj;
lean_object* v_a_407_ = stack[4].m_obj;
lean_object* v_a_408_ = stack[5].m_obj;
lean_object* v_a_409_ = stack[6].m_obj;
lean_object* v_a_410_ = stack[7].m_obj;
lean_object* v_a_411_ = stack[8].m_obj;
lean_object* v_res_421_;
v_res_421_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_403_, v_xs_404_, v_k_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___boxed(lean_object* v_addHypotheses_422_, lean_object* v_xs_423_, lean_object* v_k_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
uint8_t v_addHypotheses_boxed_432_; lean_object* v_res_433_; 
v_addHypotheses_boxed_432_ = lean_unbox(v_addHypotheses_422_);
v_res_433_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_boxed_432_, v_xs_423_, v_k_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
return v_res_433_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(uint8_t v_addHypotheses_434_, lean_object* v_00_u03b1_435_, lean_object* v_xs_436_, lean_object* v_k_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_434_, v_xs_436_, v_k_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
return v___x_445_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_addHypotheses_434_ = stack[0].m_num;
lean_object* v_xs_436_ = stack[2].m_obj;
lean_object* v_k_437_ = stack[3].m_obj;
lean_object* v_a_438_ = stack[4].m_obj;
lean_object* v_a_439_ = stack[5].m_obj;
lean_object* v_a_440_ = stack[6].m_obj;
lean_object* v_a_441_ = stack[7].m_obj;
lean_object* v_a_442_ = stack[8].m_obj;
lean_object* v_a_443_ = stack[9].m_obj;
lean_object* v_res_446_;
v_res_446_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(v_addHypotheses_434_, lean_box(0), v_xs_436_, v_k_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed(lean_object* v_addHypotheses_447_, lean_object* v_00_u03b1_448_, lean_object* v_xs_449_, lean_object* v_k_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
uint8_t v_addHypotheses_boxed_458_; lean_object* v_res_459_; 
v_addHypotheses_boxed_458_ = lean_unbox(v_addHypotheses_447_);
v_res_459_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(v_addHypotheses_boxed_458_, v_00_u03b1_448_, v_xs_449_, v_k_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(lean_object* v_k_460_, lean_object* v_v_461_, lean_object* v_t_462_){
_start:
{
if (lean_obj_tag(v_t_462_) == 0)
{
lean_object* v_size_463_; lean_object* v_k_464_; lean_object* v_v_465_; lean_object* v_l_466_; lean_object* v_r_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_748_; 
v_size_463_ = lean_ctor_get(v_t_462_, 0);
v_k_464_ = lean_ctor_get(v_t_462_, 1);
v_v_465_ = lean_ctor_get(v_t_462_, 2);
v_l_466_ = lean_ctor_get(v_t_462_, 3);
v_r_467_ = lean_ctor_get(v_t_462_, 4);
v_isSharedCheck_748_ = !lean_is_exclusive(v_t_462_);
if (v_isSharedCheck_748_ == 0)
{
v___x_469_ = v_t_462_;
v_isShared_470_ = v_isSharedCheck_748_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_r_467_);
lean_inc(v_l_466_);
lean_inc(v_v_465_);
lean_inc(v_k_464_);
lean_inc(v_size_463_);
lean_dec(v_t_462_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_748_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
uint8_t v___x_471_; 
v___x_471_ = lean_nat_dec_lt(v_k_460_, v_k_464_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = lean_nat_dec_eq(v_k_460_, v_k_464_);
if (v___x_472_ == 0)
{
lean_object* v_impl_473_; lean_object* v___x_474_; 
lean_dec(v_size_463_);
v_impl_473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_460_, v_v_461_, v_r_467_);
v___x_474_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_466_) == 0)
{
lean_object* v_size_475_; lean_object* v_size_476_; lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v_l_479_; lean_object* v_r_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_size_475_ = lean_ctor_get(v_l_466_, 0);
v_size_476_ = lean_ctor_get(v_impl_473_, 0);
v_k_477_ = lean_ctor_get(v_impl_473_, 1);
v_v_478_ = lean_ctor_get(v_impl_473_, 2);
v_l_479_ = lean_ctor_get(v_impl_473_, 3);
lean_inc(v_l_479_);
v_r_480_ = lean_ctor_get(v_impl_473_, 4);
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = lean_nat_mul(v___x_481_, v_size_475_);
v___x_483_ = lean_nat_dec_lt(v___x_482_, v_size_476_);
lean_dec(v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
lean_dec(v_l_479_);
v___x_484_ = lean_nat_add(v___x_474_, v_size_475_);
v___x_485_ = lean_nat_add(v___x_484_, v_size_476_);
lean_dec(v___x_484_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_impl_473_);
lean_ctor_set(v___x_469_, 0, v___x_485_);
v___x_487_ = v___x_469_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v_impl_473_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_552_; 
lean_inc(v_r_480_);
lean_inc(v_v_478_);
lean_inc(v_k_477_);
lean_inc(v_size_476_);
v_isSharedCheck_552_ = !lean_is_exclusive(v_impl_473_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; lean_object* v_unused_554_; lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; 
v_unused_553_ = lean_ctor_get(v_impl_473_, 4);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_impl_473_, 3);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_impl_473_, 2);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_impl_473_, 1);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_impl_473_, 0);
lean_dec(v_unused_557_);
v___x_490_ = v_impl_473_;
v_isShared_491_ = v_isSharedCheck_552_;
goto v_resetjp_489_;
}
else
{
lean_dec(v_impl_473_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_552_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_size_492_; lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v_l_495_; lean_object* v_r_496_; lean_object* v_size_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_size_492_ = lean_ctor_get(v_l_479_, 0);
v_k_493_ = lean_ctor_get(v_l_479_, 1);
v_v_494_ = lean_ctor_get(v_l_479_, 2);
v_l_495_ = lean_ctor_get(v_l_479_, 3);
v_r_496_ = lean_ctor_get(v_l_479_, 4);
v_size_497_ = lean_ctor_get(v_r_480_, 0);
v___x_498_ = lean_unsigned_to_nat(2u);
v___x_499_ = lean_nat_mul(v___x_498_, v_size_497_);
v___x_500_ = lean_nat_dec_lt(v_size_492_, v___x_499_);
lean_dec(v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_528_; 
lean_inc(v_r_496_);
lean_inc(v_l_495_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
v_isSharedCheck_528_ = !lean_is_exclusive(v_l_479_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_529_ = lean_ctor_get(v_l_479_, 4);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_l_479_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_l_479_, 2);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_l_479_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_l_479_, 0);
lean_dec(v_unused_533_);
v___x_502_ = v_l_479_;
v_isShared_503_ = v_isSharedCheck_528_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_l_479_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_528_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_518_; 
v___x_504_ = lean_nat_add(v___x_474_, v_size_475_);
v___x_505_ = lean_nat_add(v___x_504_, v_size_476_);
lean_dec(v_size_476_);
if (lean_obj_tag(v_l_495_) == 0)
{
lean_object* v_size_526_; 
v_size_526_ = lean_ctor_get(v_l_495_, 0);
lean_inc(v_size_526_);
v___y_518_ = v_size_526_;
goto v___jp_517_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___y_518_ = v___x_527_;
goto v___jp_517_;
}
v___jp_506_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_nat_add(v___y_507_, v___y_509_);
lean_dec(v___y_509_);
lean_dec(v___y_507_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 4, v_r_480_);
lean_ctor_set(v___x_502_, 3, v_r_496_);
lean_ctor_set(v___x_502_, 2, v_v_478_);
lean_ctor_set(v___x_502_, 1, v_k_477_);
lean_ctor_set(v___x_502_, 0, v___x_510_);
v___x_512_ = v___x_502_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_r_480_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 4, v___x_512_);
lean_ctor_set(v___x_490_, 3, v___y_508_);
lean_ctor_set(v___x_490_, 2, v_v_494_);
lean_ctor_set(v___x_490_, 1, v_k_493_);
lean_ctor_set(v___x_490_, 0, v___x_505_);
v___x_514_ = v___x_490_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v___y_508_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_nat_add(v___x_504_, v___y_518_);
lean_dec(v___y_518_);
lean_dec(v___x_504_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_l_495_);
lean_ctor_set(v___x_469_, 0, v___x_519_);
v___x_521_ = v___x_469_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_l_495_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_nat_add(v___x_474_, v_size_497_);
if (lean_obj_tag(v_r_496_) == 0)
{
lean_object* v_size_523_; 
v_size_523_ = lean_ctor_get(v_r_496_, 0);
lean_inc(v_size_523_);
v___y_507_ = v___x_522_;
v___y_508_ = v___x_521_;
v___y_509_ = v_size_523_;
goto v___jp_506_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_unsigned_to_nat(0u);
v___y_507_ = v___x_522_;
v___y_508_ = v___x_521_;
v___y_509_ = v___x_524_;
goto v___jp_506_;
}
}
}
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
lean_del_object(v___x_469_);
v___x_534_ = lean_nat_add(v___x_474_, v_size_475_);
v___x_535_ = lean_nat_add(v___x_534_, v_size_476_);
lean_dec(v_size_476_);
v___x_536_ = lean_nat_add(v___x_534_, v_size_492_);
lean_dec(v___x_534_);
lean_inc_ref(v_l_466_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 4, v_l_479_);
lean_ctor_set(v___x_490_, 3, v_l_466_);
lean_ctor_set(v___x_490_, 2, v_v_465_);
lean_ctor_set(v___x_490_, 1, v_k_464_);
lean_ctor_set(v___x_490_, 0, v___x_536_);
v___x_538_ = v___x_490_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_l_479_);
v___x_538_ = v_reuseFailAlloc_551_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_isSharedCheck_545_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; 
v_unused_546_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_l_466_, 2);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_l_466_, 1);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_550_);
v___x_540_ = v_l_466_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_dec(v_l_466_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 4, v_r_480_);
lean_ctor_set(v___x_540_, 3, v___x_538_);
lean_ctor_set(v___x_540_, 2, v_v_478_);
lean_ctor_set(v___x_540_, 1, v_k_477_);
lean_ctor_set(v___x_540_, 0, v___x_535_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_r_480_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_558_; 
v_l_558_ = lean_ctor_get(v_impl_473_, 3);
lean_inc(v_l_558_);
if (lean_obj_tag(v_l_558_) == 0)
{
lean_object* v_r_559_; lean_object* v_k_560_; lean_object* v_v_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_584_; 
v_r_559_ = lean_ctor_get(v_impl_473_, 4);
v_k_560_ = lean_ctor_get(v_impl_473_, 1);
v_v_561_ = lean_ctor_get(v_impl_473_, 2);
v_isSharedCheck_584_ = !lean_is_exclusive(v_impl_473_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_585_ = lean_ctor_get(v_impl_473_, 3);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_impl_473_, 0);
lean_dec(v_unused_586_);
v___x_563_ = v_impl_473_;
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_r_559_);
lean_inc(v_v_561_);
lean_inc(v_k_560_);
lean_dec(v_impl_473_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_580_; 
v_k_565_ = lean_ctor_get(v_l_558_, 1);
v_v_566_ = lean_ctor_get(v_l_558_, 2);
v_isSharedCheck_580_ = !lean_is_exclusive(v_l_558_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; 
v_unused_581_ = lean_ctor_get(v_l_558_, 4);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_l_558_, 3);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_l_558_, 0);
lean_dec(v_unused_583_);
v___x_568_ = v_l_558_;
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_v_566_);
lean_inc(v_k_565_);
lean_dec(v_l_558_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_559_, 2);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_r_559_);
lean_ctor_set(v___x_568_, 3, v_r_559_);
lean_ctor_set(v___x_568_, 2, v_v_465_);
lean_ctor_set(v___x_568_, 1, v_k_464_);
lean_ctor_set(v___x_568_, 0, v___x_474_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_r_559_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_r_559_);
v___x_572_ = v_reuseFailAlloc_579_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
lean_inc(v_r_559_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 3, v_r_559_);
lean_ctor_set(v___x_563_, 0, v___x_474_);
v___x_574_ = v___x_563_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_r_559_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_r_559_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_574_);
lean_ctor_set(v___x_469_, 3, v___x_572_);
lean_ctor_set(v___x_469_, 2, v_v_566_);
lean_ctor_set(v___x_469_, 1, v_k_565_);
lean_ctor_set(v___x_469_, 0, v___x_570_);
v___x_576_ = v___x_469_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_k_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_v_566_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
else
{
lean_object* v_r_587_; 
v_r_587_ = lean_ctor_get(v_impl_473_, 4);
lean_inc(v_r_587_);
if (lean_obj_tag(v_r_587_) == 0)
{
lean_object* v_k_588_; lean_object* v_v_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_600_; 
v_k_588_ = lean_ctor_get(v_impl_473_, 1);
v_v_589_ = lean_ctor_get(v_impl_473_, 2);
v_isSharedCheck_600_ = !lean_is_exclusive(v_impl_473_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; lean_object* v_unused_603_; 
v_unused_601_ = lean_ctor_get(v_impl_473_, 4);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_impl_473_, 3);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_impl_473_, 0);
lean_dec(v_unused_603_);
v___x_591_ = v_impl_473_;
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_v_589_);
lean_inc(v_k_588_);
lean_dec(v_impl_473_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_unsigned_to_nat(3u);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 4, v_l_558_);
lean_ctor_set(v___x_591_, 2, v_v_465_);
lean_ctor_set(v___x_591_, 1, v_k_464_);
lean_ctor_set(v___x_591_, 0, v___x_474_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_l_558_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_l_558_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_r_587_);
lean_ctor_set(v___x_469_, 3, v___x_595_);
lean_ctor_set(v___x_469_, 2, v_v_589_);
lean_ctor_set(v___x_469_, 1, v_k_588_);
lean_ctor_set(v___x_469_, 0, v___x_593_);
v___x_597_ = v___x_469_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_r_587_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(2u);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_impl_473_);
lean_ctor_set(v___x_469_, 3, v_r_587_);
lean_ctor_set(v___x_469_, 0, v___x_604_);
v___x_606_ = v___x_469_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_r_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_impl_473_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v___x_609_; 
lean_dec(v_v_465_);
lean_dec(v_k_464_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 2, v_v_461_);
lean_ctor_set(v___x_469_, 1, v_k_460_);
v___x_609_ = v___x_469_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_size_463_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_461_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_r_467_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_impl_611_; lean_object* v___x_612_; 
lean_dec(v_size_463_);
v_impl_611_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_460_, v_v_461_, v_l_466_);
v___x_612_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_467_) == 0)
{
lean_object* v_size_613_; lean_object* v_size_614_; lean_object* v_k_615_; lean_object* v_v_616_; lean_object* v_l_617_; lean_object* v_r_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_size_613_ = lean_ctor_get(v_r_467_, 0);
v_size_614_ = lean_ctor_get(v_impl_611_, 0);
v_k_615_ = lean_ctor_get(v_impl_611_, 1);
v_v_616_ = lean_ctor_get(v_impl_611_, 2);
v_l_617_ = lean_ctor_get(v_impl_611_, 3);
v_r_618_ = lean_ctor_get(v_impl_611_, 4);
lean_inc(v_r_618_);
v___x_619_ = lean_unsigned_to_nat(3u);
v___x_620_ = lean_nat_mul(v___x_619_, v_size_613_);
v___x_621_ = lean_nat_dec_lt(v___x_620_, v_size_614_);
lean_dec(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
lean_dec(v_r_618_);
v___x_622_ = lean_nat_add(v___x_612_, v_size_614_);
v___x_623_ = lean_nat_add(v___x_622_, v_size_613_);
lean_dec(v___x_622_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 3, v_impl_611_);
lean_ctor_set(v___x_469_, 0, v___x_623_);
v___x_625_ = v___x_469_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_impl_611_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_r_467_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_692_; 
lean_inc(v_l_617_);
lean_inc(v_v_616_);
lean_inc(v_k_615_);
lean_inc(v_size_614_);
v_isSharedCheck_692_ = !lean_is_exclusive(v_impl_611_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_693_ = lean_ctor_get(v_impl_611_, 4);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_impl_611_, 3);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_impl_611_, 2);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_impl_611_, 1);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_impl_611_, 0);
lean_dec(v_unused_697_);
v___x_628_ = v_impl_611_;
v_isShared_629_ = v_isSharedCheck_692_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_impl_611_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_692_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_size_630_; lean_object* v_size_631_; lean_object* v_k_632_; lean_object* v_v_633_; lean_object* v_l_634_; lean_object* v_r_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_size_630_ = lean_ctor_get(v_l_617_, 0);
v_size_631_ = lean_ctor_get(v_r_618_, 0);
v_k_632_ = lean_ctor_get(v_r_618_, 1);
v_v_633_ = lean_ctor_get(v_r_618_, 2);
v_l_634_ = lean_ctor_get(v_r_618_, 3);
v_r_635_ = lean_ctor_get(v_r_618_, 4);
v___x_636_ = lean_unsigned_to_nat(2u);
v___x_637_ = lean_nat_mul(v___x_636_, v_size_630_);
v___x_638_ = lean_nat_dec_lt(v_size_631_, v___x_637_);
lean_dec(v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_667_; 
lean_inc(v_r_635_);
lean_inc(v_l_634_);
lean_inc(v_v_633_);
lean_inc(v_k_632_);
v_isSharedCheck_667_ = !lean_is_exclusive(v_r_618_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_668_ = lean_ctor_get(v_r_618_, 4);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_r_618_, 3);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_r_618_, 2);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_r_618_, 1);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_r_618_, 0);
lean_dec(v_unused_672_);
v___x_640_ = v_r_618_;
v_isShared_641_ = v_isSharedCheck_667_;
goto v_resetjp_639_;
}
else
{
lean_dec(v_r_618_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_667_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___x_655_; lean_object* v___y_657_; 
v___x_642_ = lean_nat_add(v___x_612_, v_size_614_);
lean_dec(v_size_614_);
v___x_643_ = lean_nat_add(v___x_642_, v_size_613_);
lean_dec(v___x_642_);
v___x_655_ = lean_nat_add(v___x_612_, v_size_630_);
if (lean_obj_tag(v_l_634_) == 0)
{
lean_object* v_size_665_; 
v_size_665_ = lean_ctor_get(v_l_634_, 0);
lean_inc(v_size_665_);
v___y_657_ = v_size_665_;
goto v___jp_656_;
}
else
{
lean_object* v___x_666_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___y_657_ = v___x_666_;
goto v___jp_656_;
}
v___jp_644_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_nat_add(v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec(v___y_646_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_r_467_);
lean_ctor_set(v___x_640_, 3, v_r_635_);
lean_ctor_set(v___x_640_, 2, v_v_465_);
lean_ctor_set(v___x_640_, 1, v_k_464_);
lean_ctor_set(v___x_640_, 0, v___x_648_);
v___x_650_ = v___x_640_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_r_635_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_r_467_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_652_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v___x_650_);
lean_ctor_set(v___x_628_, 3, v___y_645_);
lean_ctor_set(v___x_628_, 2, v_v_633_);
lean_ctor_set(v___x_628_, 1, v_k_632_);
lean_ctor_set(v___x_628_, 0, v___x_643_);
v___x_652_ = v___x_628_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_k_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_v_633_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v___y_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = lean_nat_add(v___x_655_, v___y_657_);
lean_dec(v___y_657_);
lean_dec(v___x_655_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_l_634_);
lean_ctor_set(v___x_469_, 3, v_l_617_);
lean_ctor_set(v___x_469_, 2, v_v_616_);
lean_ctor_set(v___x_469_, 1, v_k_615_);
lean_ctor_set(v___x_469_, 0, v___x_658_);
v___x_660_ = v___x_469_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_615_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_616_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_l_617_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_l_634_);
v___x_660_ = v_reuseFailAlloc_664_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; 
v___x_661_ = lean_nat_add(v___x_612_, v_size_613_);
if (lean_obj_tag(v_r_635_) == 0)
{
lean_object* v_size_662_; 
v_size_662_ = lean_ctor_get(v_r_635_, 0);
lean_inc(v_size_662_);
v___y_645_ = v___x_660_;
v___y_646_ = v___x_661_;
v___y_647_ = v_size_662_;
goto v___jp_644_;
}
else
{
lean_object* v___x_663_; 
v___x_663_ = lean_unsigned_to_nat(0u);
v___y_645_ = v___x_660_;
v___y_646_ = v___x_661_;
v___y_647_ = v___x_663_;
goto v___jp_644_;
}
}
}
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
lean_del_object(v___x_469_);
v___x_673_ = lean_nat_add(v___x_612_, v_size_614_);
lean_dec(v_size_614_);
v___x_674_ = lean_nat_add(v___x_673_, v_size_613_);
lean_dec(v___x_673_);
v___x_675_ = lean_nat_add(v___x_612_, v_size_613_);
v___x_676_ = lean_nat_add(v___x_675_, v_size_631_);
lean_dec(v___x_675_);
lean_inc_ref(v_r_467_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v_r_467_);
lean_ctor_set(v___x_628_, 3, v_r_618_);
lean_ctor_set(v___x_628_, 2, v_v_465_);
lean_ctor_set(v___x_628_, 1, v_k_464_);
lean_ctor_set(v___x_628_, 0, v___x_676_);
v___x_678_ = v___x_628_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_r_618_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_r_467_);
v___x_678_ = v_reuseFailAlloc_691_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_isSharedCheck_685_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_686_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_r_467_, 2);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_r_467_, 1);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_690_);
v___x_680_ = v_r_467_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_dec(v_r_467_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 4, v___x_678_);
lean_ctor_set(v___x_680_, 3, v_l_617_);
lean_ctor_set(v___x_680_, 2, v_v_616_);
lean_ctor_set(v___x_680_, 1, v_k_615_);
lean_ctor_set(v___x_680_, 0, v___x_674_);
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_k_615_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_v_616_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_l_617_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v___x_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_698_; 
v_l_698_ = lean_ctor_get(v_impl_611_, 3);
if (lean_obj_tag(v_l_698_) == 0)
{
lean_object* v_r_699_; lean_object* v_k_700_; lean_object* v_v_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_712_; 
lean_inc_ref(v_l_698_);
v_r_699_ = lean_ctor_get(v_impl_611_, 4);
v_k_700_ = lean_ctor_get(v_impl_611_, 1);
v_v_701_ = lean_ctor_get(v_impl_611_, 2);
v_isSharedCheck_712_ = !lean_is_exclusive(v_impl_611_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_713_ = lean_ctor_get(v_impl_611_, 3);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_impl_611_, 0);
lean_dec(v_unused_714_);
v___x_703_ = v_impl_611_;
v_isShared_704_ = v_isSharedCheck_712_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_r_699_);
lean_inc(v_v_701_);
lean_inc(v_k_700_);
lean_dec(v_impl_611_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_712_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_699_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 3, v_r_699_);
lean_ctor_set(v___x_703_, 2, v_v_465_);
lean_ctor_set(v___x_703_, 1, v_k_464_);
lean_ctor_set(v___x_703_, 0, v___x_612_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_711_, 4, v_r_699_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_707_);
lean_ctor_set(v___x_469_, 3, v_l_698_);
lean_ctor_set(v___x_469_, 2, v_v_701_);
lean_ctor_set(v___x_469_, 1, v_k_700_);
lean_ctor_set(v___x_469_, 0, v___x_705_);
v___x_709_ = v___x_469_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_701_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v___x_707_);
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
else
{
lean_object* v_r_715_; 
v_r_715_ = lean_ctor_get(v_impl_611_, 4);
lean_inc(v_r_715_);
if (lean_obj_tag(v_r_715_) == 0)
{
lean_object* v_k_716_; lean_object* v_v_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_740_; 
lean_inc(v_l_698_);
v_k_716_ = lean_ctor_get(v_impl_611_, 1);
v_v_717_ = lean_ctor_get(v_impl_611_, 2);
v_isSharedCheck_740_ = !lean_is_exclusive(v_impl_611_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; lean_object* v_unused_742_; lean_object* v_unused_743_; 
v_unused_741_ = lean_ctor_get(v_impl_611_, 4);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_impl_611_, 3);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_impl_611_, 0);
lean_dec(v_unused_743_);
v___x_719_ = v_impl_611_;
v_isShared_720_ = v_isSharedCheck_740_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_v_717_);
lean_inc(v_k_716_);
lean_dec(v_impl_611_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_740_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_k_721_; lean_object* v_v_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_736_; 
v_k_721_ = lean_ctor_get(v_r_715_, 1);
v_v_722_ = lean_ctor_get(v_r_715_, 2);
v_isSharedCheck_736_ = !lean_is_exclusive(v_r_715_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; 
v_unused_737_ = lean_ctor_get(v_r_715_, 4);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_r_715_, 3);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_r_715_, 0);
lean_dec(v_unused_739_);
v___x_724_ = v_r_715_;
v_isShared_725_ = v_isSharedCheck_736_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_v_722_);
lean_inc(v_k_721_);
lean_dec(v_r_715_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_736_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_unsigned_to_nat(3u);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 4, v_l_698_);
lean_ctor_set(v___x_724_, 3, v_l_698_);
lean_ctor_set(v___x_724_, 2, v_v_717_);
lean_ctor_set(v___x_724_, 1, v_k_716_);
lean_ctor_set(v___x_724_, 0, v___x_612_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_k_716_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_v_717_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_l_698_);
v___x_728_ = v_reuseFailAlloc_735_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v_l_698_);
lean_ctor_set(v___x_719_, 2, v_v_465_);
lean_ctor_set(v___x_719_, 1, v_k_464_);
lean_ctor_set(v___x_719_, 0, v___x_612_);
v___x_730_ = v___x_719_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_l_698_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_730_);
lean_ctor_set(v___x_469_, 3, v___x_728_);
lean_ctor_set(v___x_469_, 2, v_v_722_);
lean_ctor_set(v___x_469_, 1, v_k_721_);
lean_ctor_set(v___x_469_, 0, v___x_726_);
v___x_732_ = v___x_469_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_k_721_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_v_722_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v___x_730_);
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
else
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(2u);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_r_715_);
lean_ctor_set(v___x_469_, 3, v_impl_611_);
lean_ctor_set(v___x_469_, 0, v___x_744_);
v___x_746_ = v___x_469_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_impl_611_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_r_715_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_k_460_);
lean_ctor_set(v___x_750_, 2, v_v_461_);
lean_ctor_set(v___x_750_, 3, v_t_462_);
lean_ctor_set(v___x_750_, 4, v_t_462_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(lean_object* v_t_751_, lean_object* v_k_752_){
_start:
{
if (lean_obj_tag(v_t_751_) == 0)
{
lean_object* v_k_753_; lean_object* v_v_754_; lean_object* v_l_755_; lean_object* v_r_756_; uint8_t v___x_757_; 
v_k_753_ = lean_ctor_get(v_t_751_, 1);
v_v_754_ = lean_ctor_get(v_t_751_, 2);
v_l_755_ = lean_ctor_get(v_t_751_, 3);
v_r_756_ = lean_ctor_get(v_t_751_, 4);
v___x_757_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_752_, v_k_753_);
switch(v___x_757_)
{
case 0:
{
v_t_751_ = v_l_755_;
goto _start;
}
case 1:
{
lean_object* v___x_759_; 
lean_inc(v_v_754_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v_v_754_);
return v___x_759_;
}
default: 
{
v_t_751_ = v_r_756_;
goto _start;
}
}
}
else
{
lean_object* v___x_761_; 
v___x_761_ = lean_box(0);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg___boxed(lean_object* v_t_762_, lean_object* v_k_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_762_, v_k_763_);
lean_dec(v_k_763_);
lean_dec(v_t_762_);
return v_res_764_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(lean_object* v_k_765_, lean_object* v_t_766_){
_start:
{
if (lean_obj_tag(v_t_766_) == 0)
{
lean_object* v_k_767_; lean_object* v_l_768_; lean_object* v_r_769_; uint8_t v___x_770_; 
v_k_767_ = lean_ctor_get(v_t_766_, 1);
v_l_768_ = lean_ctor_get(v_t_766_, 3);
v_r_769_ = lean_ctor_get(v_t_766_, 4);
v___x_770_ = lean_nat_dec_lt(v_k_765_, v_k_767_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = lean_nat_dec_eq(v_k_765_, v_k_767_);
if (v___x_771_ == 0)
{
v_t_766_ = v_r_769_;
goto _start;
}
else
{
return v___x_771_;
}
}
else
{
v_t_766_ = v_l_768_;
goto _start;
}
}
else
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_765_ = stack[0].m_obj;
lean_object* v_t_766_ = stack[1].m_obj;
uint8_t v_res_775_;
v_res_775_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_765_, v_t_766_);
stack->m_num = v_res_775_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg___boxed(lean_object* v_k_776_, lean_object* v_t_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_776_, v_t_777_);
lean_dec(v_t_777_);
lean_dec(v_k_776_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(lean_object* v_localInst2Index_780_, lean_object* v_e_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_fvarId_784_; lean_object* v___x_785_; 
v_fvarId_784_ = l_Lean_Expr_fvarId_x21(v_e_781_);
v___x_785_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_localInst2Index_780_, v_fvarId_784_);
lean_dec(v_fvarId_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; 
v___x_786_ = lean_box(0);
return v___x_786_;
}
else
{
lean_object* v_val_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___y_791_; uint8_t v___x_793_; 
v_val_787_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v___x_785_, 1);
v___x_788_ = lean_st_ref_take(v___y_782_);
v___x_789_ = lean_box(0);
v___x_793_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_val_787_, v___x_788_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_val_787_, v___x_789_, v___x_788_);
v___y_791_ = v___x_794_;
goto v___jp_790_;
}
else
{
lean_dec(v_val_787_);
v___y_791_ = v___x_788_;
goto v___jp_790_;
}
v___jp_790_:
{
lean_object* v___x_792_; 
v___x_792_ = lean_st_ref_put(v___y_782_, v___y_791_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_localInst2Index_780_ = stack[0].m_obj;
lean_object* v_e_781_ = stack[1].m_obj;
lean_object* v___y_782_ = stack[2].m_obj;
lean_object* v_res_795_;
v_res_795_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(v_localInst2Index_780_, v_e_781_, v___y_782_);
stack->m_obj
 = v_res_795_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed(lean_object* v_localInst2Index_796_, lean_object* v_e_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(v_localInst2Index_796_, v_e_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v_e_797_);
lean_dec(v_localInst2Index_796_);
return v_res_800_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
else
{
lean_object* v_key_804_; lean_object* v_tail_805_; uint8_t v___x_806_; 
v_key_804_ = lean_ctor_get(v_x_802_, 0);
v_tail_805_ = lean_ctor_get(v_x_802_, 2);
v___x_806_ = lean_expr_eqv(v_key_804_, v_a_801_);
if (v___x_806_ == 0)
{
v_x_802_ = v_tail_805_;
goto _start;
}
else
{
return v___x_806_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_801_ = stack[0].m_obj;
lean_object* v_x_802_ = stack[1].m_obj;
uint8_t v_res_808_;
v_res_808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_801_, v_x_802_);
stack->m_num = v_res_808_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_a_809_, lean_object* v_x_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_809_, v_x_810_);
lean_dec(v_x_810_);
lean_dec_ref(v_a_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
return v_x_813_;
}
else
{
lean_object* v_key_815_; lean_object* v_value_816_; lean_object* v_tail_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_840_; 
v_key_815_ = lean_ctor_get(v_x_814_, 0);
v_value_816_ = lean_ctor_get(v_x_814_, 1);
v_tail_817_ = lean_ctor_get(v_x_814_, 2);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_814_);
if (v_isSharedCheck_840_ == 0)
{
v___x_819_ = v_x_814_;
v_isShared_820_ = v_isSharedCheck_840_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_tail_817_);
lean_inc(v_value_816_);
lean_inc(v_key_815_);
lean_dec(v_x_814_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_840_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v_fold_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_821_ = lean_array_get_size(v_x_813_);
v___x_822_ = l_Lean_Expr_hash(v_key_815_);
v___x_823_ = 32ULL;
v___x_824_ = lean_uint64_shift_right(v___x_822_, v___x_823_);
v_fold_825_ = lean_uint64_xor(v___x_822_, v___x_824_);
v___x_826_ = 16ULL;
v___x_827_ = lean_uint64_shift_right(v_fold_825_, v___x_826_);
v___x_828_ = lean_uint64_xor(v_fold_825_, v___x_827_);
v___x_829_ = lean_uint64_to_usize(v___x_828_);
v___x_830_ = lean_usize_of_nat(v___x_821_);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_sub(v___x_830_, v___x_831_);
v___x_833_ = lean_usize_land(v___x_829_, v___x_832_);
v___x_834_ = lean_array_uget_borrowed(v_x_813_, v___x_833_);
lean_inc(v___x_834_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 2, v___x_834_);
v___x_836_ = v___x_819_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_key_815_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_value_816_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v___x_834_);
v___x_836_ = v_reuseFailAlloc_839_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_array_uset(v_x_813_, v___x_833_, v___x_836_);
v_x_813_ = v___x_837_;
v_x_814_ = v_tail_817_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_i_841_, lean_object* v_source_842_, lean_object* v_target_843_){
_start:
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_array_get_size(v_source_842_);
v___x_845_ = lean_nat_dec_lt(v_i_841_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec_ref(v_source_842_);
lean_dec(v_i_841_);
return v_target_843_;
}
else
{
lean_object* v_es_846_; lean_object* v___x_847_; lean_object* v_source_848_; lean_object* v_target_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_es_846_ = lean_array_fget(v_source_842_, v_i_841_);
v___x_847_ = lean_box(0);
v_source_848_ = lean_array_fset(v_source_842_, v_i_841_, v___x_847_);
v_target_849_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_target_843_, v_es_846_);
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_add(v_i_841_, v___x_850_);
lean_dec(v_i_841_);
v_i_841_ = v___x_851_;
v_source_842_ = v_source_848_;
v_target_843_ = v_target_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_data_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_nbuckets_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_854_ = lean_array_get_size(v_data_853_);
v___x_855_ = lean_unsigned_to_nat(2u);
v_nbuckets_856_ = lean_nat_mul(v___x_854_, v___x_855_);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_box(0);
v___x_859_ = lean_mk_array(v_nbuckets_856_, v___x_858_);
v___x_860_ = lean_array_propagate_mark(v_data_853_, v___x_859_);
v___x_861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v___x_857_, v_data_853_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(lean_object* v_m_862_, lean_object* v_a_863_, lean_object* v_b_864_){
_start:
{
lean_object* v_size_865_; lean_object* v_buckets_866_; lean_object* v___x_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; uint64_t v_fold_871_; uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v_bkt_880_; uint8_t v___x_881_; 
v_size_865_ = lean_ctor_get(v_m_862_, 0);
v_buckets_866_ = lean_ctor_get(v_m_862_, 1);
v___x_867_ = lean_array_get_size(v_buckets_866_);
v___x_868_ = l_Lean_Expr_hash(v_a_863_);
v___x_869_ = 32ULL;
v___x_870_ = lean_uint64_shift_right(v___x_868_, v___x_869_);
v_fold_871_ = lean_uint64_xor(v___x_868_, v___x_870_);
v___x_872_ = 16ULL;
v___x_873_ = lean_uint64_shift_right(v_fold_871_, v___x_872_);
v___x_874_ = lean_uint64_xor(v_fold_871_, v___x_873_);
v___x_875_ = lean_uint64_to_usize(v___x_874_);
v___x_876_ = lean_usize_of_nat(v___x_867_);
v___x_877_ = ((size_t)1ULL);
v___x_878_ = lean_usize_sub(v___x_876_, v___x_877_);
v___x_879_ = lean_usize_land(v___x_875_, v___x_878_);
v_bkt_880_ = lean_array_uget_borrowed(v_buckets_866_, v___x_879_);
v___x_881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_863_, v_bkt_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_902_; 
lean_inc_ref(v_buckets_866_);
lean_inc(v_size_865_);
v_isSharedCheck_902_ = !lean_is_exclusive(v_m_862_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; lean_object* v_unused_904_; 
v_unused_903_ = lean_ctor_get(v_m_862_, 1);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_m_862_, 0);
lean_dec(v_unused_904_);
v___x_883_ = v_m_862_;
v_isShared_884_ = v_isSharedCheck_902_;
goto v_resetjp_882_;
}
else
{
lean_dec(v_m_862_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_902_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v_size_x27_886_; lean_object* v___x_887_; lean_object* v_buckets_x27_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_885_ = lean_unsigned_to_nat(1u);
v_size_x27_886_ = lean_nat_add(v_size_865_, v___x_885_);
lean_dec(v_size_865_);
lean_inc(v_bkt_880_);
v___x_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_887_, 0, v_a_863_);
lean_ctor_set(v___x_887_, 1, v_b_864_);
lean_ctor_set(v___x_887_, 2, v_bkt_880_);
v_buckets_x27_888_ = lean_array_uset(v_buckets_866_, v___x_879_, v___x_887_);
v___x_889_ = lean_unsigned_to_nat(4u);
v___x_890_ = lean_nat_mul(v_size_x27_886_, v___x_889_);
v___x_891_ = lean_unsigned_to_nat(3u);
v___x_892_ = lean_nat_div(v___x_890_, v___x_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_array_get_size(v_buckets_x27_888_);
v___x_894_ = lean_nat_dec_le(v___x_892_, v___x_893_);
lean_dec(v___x_892_);
if (v___x_894_ == 0)
{
lean_object* v_val_895_; lean_object* v___x_897_; 
v_val_895_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_buckets_x27_888_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_val_895_);
lean_ctor_set(v___x_883_, 0, v_size_x27_886_);
v___x_897_ = v___x_883_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_size_x27_886_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_val_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_object* v___x_900_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_buckets_x27_888_);
lean_ctor_set(v___x_883_, 0, v_size_x27_886_);
v___x_900_ = v___x_883_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_size_x27_886_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_buckets_x27_888_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_dec(v_b_864_);
lean_dec_ref(v_a_863_);
return v_m_862_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(lean_object* v_m_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_buckets_907_; lean_object* v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v_fold_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_buckets_907_ = lean_ctor_get(v_m_905_, 1);
v___x_908_ = lean_array_get_size(v_buckets_907_);
v___x_909_ = l_Lean_Expr_hash(v_a_906_);
v___x_910_ = 32ULL;
v___x_911_ = lean_uint64_shift_right(v___x_909_, v___x_910_);
v_fold_912_ = lean_uint64_xor(v___x_909_, v___x_911_);
v___x_913_ = 16ULL;
v___x_914_ = lean_uint64_shift_right(v_fold_912_, v___x_913_);
v___x_915_ = lean_uint64_xor(v_fold_912_, v___x_914_);
v___x_916_ = lean_uint64_to_usize(v___x_915_);
v___x_917_ = lean_usize_of_nat(v___x_908_);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_sub(v___x_917_, v___x_918_);
v___x_920_ = lean_usize_land(v___x_916_, v___x_919_);
v___x_921_ = lean_array_uget_borrowed(v_buckets_907_, v___x_920_);
v___x_922_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_906_, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_905_ = stack[0].m_obj;
lean_object* v_a_906_ = stack[1].m_obj;
uint8_t v_res_923_;
v_res_923_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_905_, v_a_906_);
stack->m_num = v_res_923_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_m_924_, lean_object* v_a_925_){
_start:
{
uint8_t v_res_926_; lean_object* v_r_927_; 
v_res_926_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_924_, v_a_925_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v_m_924_);
v_r_927_ = lean_box(v_res_926_);
return v_r_927_;
}
}
uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(lean_object* v_e_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; lean_object* v_checked_932_; uint8_t v___x_933_; 
v___x_931_ = lean_st_ref_get(v_a_929_);
v_checked_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc_ref(v_checked_932_);
lean_dec(v___x_931_);
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_checked_932_, v_e_928_);
lean_dec_ref(v_checked_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v_visited_935_; lean_object* v_checked_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_946_; 
v___x_934_ = lean_st_ref_take(v_a_929_);
v_visited_935_ = lean_ctor_get(v___x_934_, 0);
v_checked_936_ = lean_ctor_get(v___x_934_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_946_ == 0)
{
v___x_938_ = v___x_934_;
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_checked_936_);
lean_inc(v_visited_935_);
lean_dec(v___x_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_box(0);
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_checked_936_, v_e_928_, v___x_940_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_visited_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_945_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_st_ref_put(v_a_929_, v___x_943_);
return v___x_933_;
}
}
}
else
{
lean_dec_ref(v_e_928_);
return v___x_933_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_928_ = stack[0].m_obj;
lean_object* v_a_929_ = stack[1].m_obj;
uint8_t v_res_947_;
v_res_947_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_928_, v_a_929_);
stack->m_num = v_res_947_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_e_948_, lean_object* v_a_949_, lean_object* v___y_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_948_, v_a_949_);
lean_dec(v_a_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(lean_object* v_e_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_visited_957_; size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; size_t v___x_962_; uint8_t v___x_963_; 
v___x_956_ = lean_st_ref_get(v_a_954_);
v_visited_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_visited_957_);
lean_dec(v___x_956_);
v___x_958_ = lean_ptr_addr(v_e_953_);
v___x_959_ = ((size_t)8191ULL);
v___x_960_ = lean_usize_mod(v___x_958_, v___x_959_);
v___x_961_ = lean_array_uget(v_visited_957_, v___x_960_);
lean_dec_ref(v_visited_957_);
v___x_962_ = lean_ptr_addr(v___x_961_);
lean_dec(v___x_961_);
v___x_963_ = lean_usize_dec_eq(v___x_962_, v___x_958_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v_visited_965_; lean_object* v_checked_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v___x_964_ = lean_st_ref_take(v_a_954_);
v_visited_965_ = lean_ctor_get(v___x_964_, 0);
v_checked_966_ = lean_ctor_get(v___x_964_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_975_ == 0)
{
v___x_968_ = v___x_964_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_checked_966_);
lean_inc(v_visited_965_);
lean_dec(v___x_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_array_uset(v_visited_965_, v___x_960_, v_e_953_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_checked_966_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_st_ref_put(v_a_954_, v___x_972_);
return v___x_963_;
}
}
}
else
{
lean_dec_ref(v_e_953_);
return v___x_963_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_953_ = stack[0].m_obj;
lean_object* v_a_954_ = stack[1].m_obj;
uint8_t v_res_976_;
v_res_976_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_953_, v_a_954_);
stack->m_num = v_res_976_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_e_977_, lean_object* v_a_978_, lean_object* v___y_979_){
_start:
{
uint8_t v_res_980_; lean_object* v_r_981_; 
v_res_980_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_977_, v_a_978_);
lean_dec(v_a_978_);
v_r_981_ = lean_box(v_res_980_);
return v_r_981_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(lean_object* v_p_982_, lean_object* v_f_983_, uint8_t v_stopWhenVisited_984_, lean_object* v_e_985_, lean_object* v_a_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___y_990_; lean_object* v_d_991_; lean_object* v_b_992_; lean_object* v___y_993_; lean_object* v___y_997_; lean_object* v___y_998_; uint8_t v___x_1018_; 
lean_inc_ref(v_e_985_);
v___x_1018_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_985_, v_a_986_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
lean_inc_ref(v_p_982_);
lean_inc_ref(v_e_985_);
v___x_1019_ = lean_apply_1(v_p_982_, v_e_985_);
v___x_1020_ = lean_unbox(v___x_1019_);
if (v___x_1020_ == 0)
{
v___y_997_ = v_a_986_;
v___y_998_ = v___y_987_;
goto v___jp_996_;
}
else
{
uint8_t v___x_1021_; 
lean_inc_ref(v_e_985_);
v___x_1021_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_985_, v_a_986_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
lean_inc_ref(v_f_983_);
lean_inc(v___y_987_);
lean_inc_ref(v_e_985_);
v___x_1022_ = lean_apply_3(v_f_983_, v_e_985_, v___y_987_, lean_box(0));
if (v_stopWhenVisited_984_ == 0)
{
v___y_997_ = v_a_986_;
v___y_998_ = v___y_987_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1023_; 
lean_dec_ref(v_e_985_);
lean_dec_ref(v_f_983_);
lean_dec_ref(v_p_982_);
v___x_1023_ = lean_box(0);
return v___x_1023_;
}
}
else
{
v___y_997_ = v_a_986_;
v___y_998_ = v___y_987_;
goto v___jp_996_;
}
}
}
else
{
lean_object* v___x_1024_; 
lean_dec_ref(v_e_985_);
lean_dec_ref(v_f_983_);
lean_dec_ref(v_p_982_);
v___x_1024_ = lean_box(0);
return v___x_1024_;
}
v___jp_989_:
{
lean_object* v___x_994_; 
lean_inc_ref(v_f_983_);
lean_inc_ref(v_p_982_);
v___x_994_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_982_, v_f_983_, v_stopWhenVisited_984_, v_d_991_, v___y_993_, v___y_990_);
v_e_985_ = v_b_992_;
v_a_986_ = v___y_993_;
v___y_987_ = v___y_990_;
goto _start;
}
v___jp_996_:
{
switch(lean_obj_tag(v_e_985_))
{
case 7:
{
lean_object* v_binderType_999_; lean_object* v_body_1000_; 
v_binderType_999_ = lean_ctor_get(v_e_985_, 1);
lean_inc_ref(v_binderType_999_);
v_body_1000_ = lean_ctor_get(v_e_985_, 2);
lean_inc_ref(v_body_1000_);
lean_dec_ref_known(v_e_985_, 3);
v___y_990_ = v___y_998_;
v_d_991_ = v_binderType_999_;
v_b_992_ = v_body_1000_;
v___y_993_ = v___y_997_;
goto v___jp_989_;
}
case 6:
{
lean_object* v_binderType_1001_; lean_object* v_body_1002_; 
v_binderType_1001_ = lean_ctor_get(v_e_985_, 1);
lean_inc_ref(v_binderType_1001_);
v_body_1002_ = lean_ctor_get(v_e_985_, 2);
lean_inc_ref(v_body_1002_);
lean_dec_ref_known(v_e_985_, 3);
v___y_990_ = v___y_998_;
v_d_991_ = v_binderType_1001_;
v_b_992_ = v_body_1002_;
v___y_993_ = v___y_997_;
goto v___jp_989_;
}
case 8:
{
lean_object* v_type_1003_; lean_object* v_value_1004_; lean_object* v_body_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_type_1003_ = lean_ctor_get(v_e_985_, 1);
lean_inc_ref(v_type_1003_);
v_value_1004_ = lean_ctor_get(v_e_985_, 2);
lean_inc_ref(v_value_1004_);
v_body_1005_ = lean_ctor_get(v_e_985_, 3);
lean_inc_ref(v_body_1005_);
lean_dec_ref_known(v_e_985_, 4);
lean_inc_ref_n(v_f_983_, 2);
lean_inc_ref_n(v_p_982_, 2);
v___x_1006_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_982_, v_f_983_, v_stopWhenVisited_984_, v_type_1003_, v___y_997_, v___y_998_);
v___x_1007_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_982_, v_f_983_, v_stopWhenVisited_984_, v_value_1004_, v___y_997_, v___y_998_);
v_e_985_ = v_body_1005_;
v_a_986_ = v___y_997_;
v___y_987_ = v___y_998_;
goto _start;
}
case 5:
{
lean_object* v_fn_1009_; lean_object* v_arg_1010_; lean_object* v___x_1011_; 
v_fn_1009_ = lean_ctor_get(v_e_985_, 0);
lean_inc_ref(v_fn_1009_);
v_arg_1010_ = lean_ctor_get(v_e_985_, 1);
lean_inc_ref(v_arg_1010_);
lean_dec_ref_known(v_e_985_, 2);
lean_inc_ref(v_f_983_);
lean_inc_ref(v_p_982_);
v___x_1011_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_982_, v_f_983_, v_stopWhenVisited_984_, v_fn_1009_, v___y_997_, v___y_998_);
v_e_985_ = v_arg_1010_;
v_a_986_ = v___y_997_;
v___y_987_ = v___y_998_;
goto _start;
}
case 10:
{
lean_object* v_expr_1013_; 
v_expr_1013_ = lean_ctor_get(v_e_985_, 1);
lean_inc_ref(v_expr_1013_);
lean_dec_ref_known(v_e_985_, 2);
v_e_985_ = v_expr_1013_;
v_a_986_ = v___y_997_;
v___y_987_ = v___y_998_;
goto _start;
}
case 11:
{
lean_object* v_struct_1015_; 
v_struct_1015_ = lean_ctor_get(v_e_985_, 2);
lean_inc_ref(v_struct_1015_);
lean_dec_ref_known(v_e_985_, 3);
v_e_985_ = v_struct_1015_;
v_a_986_ = v___y_997_;
v___y_987_ = v___y_998_;
goto _start;
}
default: 
{
lean_object* v___x_1017_; 
lean_dec_ref(v_e_985_);
lean_dec_ref(v_f_983_);
lean_dec_ref(v_p_982_);
v___x_1017_ = lean_box(0);
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_982_ = stack[0].m_obj;
lean_object* v_f_983_ = stack[1].m_obj;
uint8_t v_stopWhenVisited_984_ = stack[2].m_num;
lean_object* v_e_985_ = stack[3].m_obj;
lean_object* v_a_986_ = stack[4].m_obj;
lean_object* v___y_987_ = stack[5].m_obj;
lean_object* v_res_1025_;
v_res_1025_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_982_, v_f_983_, v_stopWhenVisited_984_, v_e_985_, v_a_986_, v___y_987_);
stack->m_obj
 = v_res_1025_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg___boxed(lean_object* v_p_1026_, lean_object* v_f_1027_, lean_object* v_stopWhenVisited_1028_, lean_object* v_e_1029_, lean_object* v_a_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1033_; lean_object* v_res_1034_; 
v_stopWhenVisited_boxed_1033_ = lean_unbox(v_stopWhenVisited_1028_);
v_res_1034_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1026_, v_f_1027_, v_stopWhenVisited_boxed_1033_, v_e_1029_, v_a_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec(v_a_1030_);
return v_res_1034_;
}
}
lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(lean_object* v_p_1035_, lean_object* v_f_1036_, lean_object* v_e_1037_, uint8_t v_stopWhenVisited_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = l_Lean_ForEachExprWhere_initCache;
v___x_1042_ = lean_st_mk_ref(v___x_1041_);
v___x_1043_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1035_, v_f_1036_, v_stopWhenVisited_1038_, v_e_1037_, v___x_1042_, v___y_1039_);
v___x_1044_ = lean_st_ref_get(v___x_1042_);
lean_dec(v___x_1042_);
lean_dec(v___x_1044_);
return v___x_1043_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1035_ = stack[0].m_obj;
lean_object* v_f_1036_ = stack[1].m_obj;
lean_object* v_e_1037_ = stack[2].m_obj;
uint8_t v_stopWhenVisited_1038_ = stack[3].m_num;
lean_object* v___y_1039_ = stack[4].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1035_, v_f_1036_, v_e_1037_, v_stopWhenVisited_1038_, v___y_1039_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg___boxed(lean_object* v_p_1046_, lean_object* v_f_1047_, lean_object* v_e_1048_, lean_object* v_stopWhenVisited_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1052_; lean_object* v_res_1053_; 
v_stopWhenVisited_boxed_1052_ = lean_unbox(v_stopWhenVisited_1049_);
v_res_1053_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1046_, v_f_1047_, v_e_1048_, v_stopWhenVisited_boxed_1052_, v___y_1050_);
lean_dec(v___y_1050_);
return v_res_1053_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(lean_object* v_usedInstIdxs_1055_, lean_object* v___f_1056_, lean_object* v_e_1057_, uint8_t v___x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1061_ = lean_st_mk_ref(v_usedInstIdxs_1055_);
v___x_1062_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0));
v___x_1063_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v___x_1062_, v___f_1056_, v_e_1057_, v___x_1058_, v___x_1061_);
v___x_1064_ = lean_st_ref_get(v___x_1061_);
lean_dec(v___x_1061_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_usedInstIdxs_1055_ = stack[0].m_obj;
lean_object* v___f_1056_ = stack[1].m_obj;
lean_object* v_e_1057_ = stack[2].m_obj;
uint8_t v___x_1058_ = stack[3].m_num;
lean_object* v_res_1066_;
v_res_1066_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(v_usedInstIdxs_1055_, v___f_1056_, v_e_1057_, v___x_1058_, lean_box(0));
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed(lean_object* v_usedInstIdxs_1067_, lean_object* v___f_1068_, lean_object* v_e_1069_, lean_object* v___x_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v___x_7330__boxed_1073_; lean_object* v_res_1074_; 
v___x_7330__boxed_1073_ = lean_unbox(v___x_1070_);
v_res_1074_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(v_usedInstIdxs_1067_, v___f_1068_, v_e_1069_, v___x_7330__boxed_1073_, v_x_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(lean_object* v_usedInstIdxs_1075_, lean_object* v_localInst2Index_1076_, lean_object* v_e_1077_){
_start:
{
if (lean_obj_tag(v_localInst2Index_1076_) == 0)
{
lean_object* v___f_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v_snd_1083_; 
v___f_1078_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1078_, 0, v_localInst2Index_1076_);
v___x_1079_ = 0;
v___x_1080_ = lean_box(v___x_1079_);
v___f_1081_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1081_, 0, v_usedInstIdxs_1075_);
lean_closure_set(v___f_1081_, 1, v___f_1078_);
lean_closure_set(v___f_1081_, 2, v_e_1077_);
lean_closure_set(v___f_1081_, 3, v___x_1080_);
v___x_1082_ = l_runST___redArg(v___f_1081_);
v_snd_1083_ = lean_ctor_get(v___x_1082_, 1);
lean_inc(v_snd_1083_);
lean_dec(v___x_1082_);
return v_snd_1083_;
}
else
{
lean_dec_ref(v_e_1077_);
return v_usedInstIdxs_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(lean_object* v_00_u03b4_1084_, lean_object* v_t_1085_, lean_object* v_k_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_1085_, v_k_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___boxed(lean_object* v_00_u03b4_1088_, lean_object* v_t_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(v_00_u03b4_1088_, v_t_1089_, v_k_1090_);
lean_dec(v_k_1090_);
lean_dec(v_t_1089_);
return v_res_1091_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(lean_object* v_00_u03b2_1092_, lean_object* v_k_1093_, lean_object* v_t_1094_){
_start:
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_1093_, v_t_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1093_ = stack[1].m_obj;
lean_object* v_t_1094_ = stack[2].m_obj;
uint8_t v_res_1096_;
v_res_1096_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(lean_box(0), v_k_1093_, v_t_1094_);
stack->m_num = v_res_1096_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___boxed(lean_object* v_00_u03b2_1097_, lean_object* v_k_1098_, lean_object* v_t_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(v_00_u03b2_1097_, v_k_1098_, v_t_1099_);
lean_dec(v_t_1099_);
lean_dec(v_k_1098_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2(lean_object* v_00_u03b2_1102_, lean_object* v_k_1103_, lean_object* v_v_1104_, lean_object* v_t_1105_, lean_object* v_hl_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_1103_, v_v_1104_, v_t_1105_);
return v___x_1107_;
}
}
lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(lean_object* v_x_1108_, lean_object* v_p_1109_, lean_object* v_f_1110_, lean_object* v_e_1111_, uint8_t v_stopWhenVisited_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1109_, v_f_1110_, v_e_1111_, v_stopWhenVisited_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1109_ = stack[1].m_obj;
lean_object* v_f_1110_ = stack[2].m_obj;
lean_object* v_e_1111_ = stack[3].m_obj;
uint8_t v_stopWhenVisited_1112_ = stack[4].m_num;
lean_object* v___y_1113_ = stack[5].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(lean_box(0), v_p_1109_, v_f_1110_, v_e_1111_, v_stopWhenVisited_1112_, v___y_1113_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___boxed(lean_object* v_x_1117_, lean_object* v_p_1118_, lean_object* v_f_1119_, lean_object* v_e_1120_, lean_object* v_stopWhenVisited_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1124_; lean_object* v_res_1125_; 
v_stopWhenVisited_boxed_1124_ = lean_unbox(v_stopWhenVisited_1121_);
v_res_1125_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(v_x_1117_, v_p_1118_, v_f_1119_, v_e_1120_, v_stopWhenVisited_boxed_1124_, v___y_1122_);
lean_dec(v___y_1122_);
return v_res_1125_;
}
}
uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(lean_object* v_x_1126_, lean_object* v_e_1127_, lean_object* v_a_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_1127_, v_a_1128_);
return v___x_1131_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1127_ = stack[1].m_obj;
lean_object* v_a_1128_ = stack[2].m_obj;
lean_object* v___y_1129_ = stack[3].m_obj;
uint8_t v_res_1132_;
v_res_1132_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(lean_box(0), v_e_1127_, v_a_1128_, v___y_1129_);
stack->m_num = v_res_1132_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___boxed(lean_object* v_x_1133_, lean_object* v_e_1134_, lean_object* v_a_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(v_x_1133_, v_e_1134_, v_a_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec(v_a_1135_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(lean_object* v_x_1140_, lean_object* v_p_1141_, lean_object* v_f_1142_, uint8_t v_stopWhenVisited_1143_, lean_object* v_e_1144_, lean_object* v_a_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1141_, v_f_1142_, v_stopWhenVisited_1143_, v_e_1144_, v_a_1145_, v___y_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1141_ = stack[1].m_obj;
lean_object* v_f_1142_ = stack[2].m_obj;
uint8_t v_stopWhenVisited_1143_ = stack[3].m_num;
lean_object* v_e_1144_ = stack[4].m_obj;
lean_object* v_a_1145_ = stack[5].m_obj;
lean_object* v___y_1146_ = stack[6].m_obj;
lean_object* v_res_1149_;
v_res_1149_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(lean_box(0), v_p_1141_, v_f_1142_, v_stopWhenVisited_1143_, v_e_1144_, v_a_1145_, v___y_1146_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___boxed(lean_object* v_x_1150_, lean_object* v_p_1151_, lean_object* v_f_1152_, lean_object* v_stopWhenVisited_1153_, lean_object* v_e_1154_, lean_object* v_a_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1158_; lean_object* v_res_1159_; 
v_stopWhenVisited_boxed_1158_ = lean_unbox(v_stopWhenVisited_1153_);
v_res_1159_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(v_x_1150_, v_p_1151_, v_f_1152_, v_stopWhenVisited_boxed_1158_, v_e_1154_, v_a_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec(v_a_1155_);
return v_res_1159_;
}
}
uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(lean_object* v_x_1160_, lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_1161_, v_a_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1161_ = stack[1].m_obj;
lean_object* v_a_1162_ = stack[2].m_obj;
lean_object* v___y_1163_ = stack[3].m_obj;
uint8_t v_res_1166_;
v_res_1166_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(lean_box(0), v_e_1161_, v_a_1162_, v___y_1163_);
stack->m_num = v_res_1166_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___boxed(lean_object* v_x_1167_, lean_object* v_e_1168_, lean_object* v_a_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v_res_1172_; lean_object* v_r_1173_; 
v_res_1172_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(v_x_1167_, v_e_1168_, v_a_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec(v_a_1169_);
v_r_1173_ = lean_box(v_res_1172_);
return v_r_1173_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1174_, lean_object* v_m_1175_, lean_object* v_a_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_1175_, v_a_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1175_ = stack[1].m_obj;
lean_object* v_a_1176_ = stack[2].m_obj;
uint8_t v_res_1178_;
v_res_1178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(lean_box(0), v_m_1175_, v_a_1176_);
stack->m_num = v_res_1178_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1179_, lean_object* v_m_1180_, lean_object* v_a_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(v_00_u03b2_1179_, v_m_1180_, v_a_1181_);
lean_dec_ref(v_a_1181_);
lean_dec_ref(v_m_1180_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1184_, lean_object* v_m_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_m_1185_, v_a_1186_, v_b_1187_);
return v___x_1188_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1189_, lean_object* v_a_1190_, lean_object* v_x_1191_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_1190_, v_x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1190_ = stack[1].m_obj;
lean_object* v_x_1191_ = stack[2].m_obj;
uint8_t v_res_1193_;
v_res_1193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_box(0), v_a_1190_, v_x_1191_);
stack->m_num = v_res_1193_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1194_, lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(v_00_u03b2_1194_, v_a_1195_, v_x_1196_);
lean_dec(v_x_1196_);
lean_dec_ref(v_a_1195_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_1199_, lean_object* v_data_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_data_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1202_, lean_object* v_i_1203_, lean_object* v_source_1204_, lean_object* v_target_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_i_1203_, v_source_1204_, v_target_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11(lean_object* v_00_u03b2_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_x_1208_, v_x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10(void){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Array_mkArray0___redArg();
return v___x_1227_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0));
v___x_1243_ = l_String_toRawSubstring_x27(v___x_1242_);
return v___x_1243_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(lean_object* v_upperBound_1256_, lean_object* v_usedInstIdxs_1257_, lean_object* v_a_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_a_1264_; uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_lt(v_a_1258_, v_upperBound_1256_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_dec(v_a_1258_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_b_1259_);
return v___x_1269_;
}
else
{
lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1326_; 
v_fst_1270_ = lean_ctor_get(v_b_1259_, 0);
v_snd_1271_ = lean_ctor_get(v_b_1259_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_b_1259_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1273_ = v_b_1259_;
v_isShared_1274_ = v_isSharedCheck_1326_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_inc(v_fst_1270_);
lean_dec(v_b_1259_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1326_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1));
v___x_1276_ = l_Lean_Core_mkFreshUserName(v___x_1275_, v___y_1260_, v___y_1261_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v_toCold_1278_; lean_object* v_ref_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v_toCold_1278_ = lean_ctor_get(v___y_1260_, 0);
v_ref_1279_ = lean_ctor_get(v___y_1260_, 2);
v___x_1280_ = l_Lean_mkIdent(v_a_1277_);
lean_inc(v___x_1280_);
v___x_1281_ = lean_array_push(v_fst_1270_, v___x_1280_);
v___x_1282_ = 0;
v___x_1283_ = l_Lean_SourceInfo_fromRef(v_ref_1279_, v___x_1282_);
v___x_1284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6));
v___x_1285_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_1283_, 5);
v___x_1286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1283_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1288_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1287_, v___x_1280_);
v___x_1289_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1283_);
lean_ctor_set(v___x_1290_, 1, v___x_1287_);
lean_ctor_set(v___x_1290_, 2, v___x_1289_);
v___x_1291_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_1292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1283_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_inc_ref(v___x_1290_);
lean_inc(v___x_1288_);
v___x_1293_ = l_Lean_Syntax_node4(v___x_1283_, v___x_1284_, v___x_1286_, v___x_1288_, v___x_1290_, v___x_1292_);
v___x_1294_ = lean_array_push(v_snd_1271_, v___x_1293_);
v___x_1295_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_a_1258_, v_usedInstIdxs_1257_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1297_; 
lean_dec_ref_known(v___x_1290_, 3);
lean_dec(v___x_1288_);
lean_dec(v___x_1283_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1294_);
lean_ctor_set(v___x_1273_, 0, v___x_1281_);
v___x_1297_ = v___x_1273_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1294_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v_a_1264_ = v___x_1297_;
goto v___jp_1263_;
}
}
else
{
lean_object* v_quotContext_1299_; lean_object* v_currMacroScope_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v_quotContext_1299_ = lean_ctor_get(v_toCold_1278_, 8);
v_currMacroScope_1300_ = lean_ctor_get(v_toCold_1278_, 9);
v___x_1301_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13));
v___x_1302_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14));
lean_inc_n(v___x_1283_, 4);
v___x_1303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1283_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1305_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1306_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1300_);
lean_inc(v_quotContext_1299_);
v___x_1307_ = l_Lean_addMacroScope(v_quotContext_1299_, v___x_1306_, v_currMacroScope_1300_);
v___x_1308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1309_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1283_);
lean_ctor_set(v___x_1309_, 1, v___x_1305_);
lean_ctor_set(v___x_1309_, 2, v___x_1307_);
lean_ctor_set(v___x_1309_, 3, v___x_1308_);
v___x_1310_ = l_Lean_Syntax_node2(v___x_1283_, v___x_1304_, v___x_1309_, v___x_1288_);
v___x_1311_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22));
v___x_1312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1283_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_Syntax_node4(v___x_1283_, v___x_1301_, v___x_1303_, v___x_1290_, v___x_1310_, v___x_1312_);
v___x_1314_ = lean_array_push(v___x_1294_, v___x_1313_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1314_);
lean_ctor_set(v___x_1273_, 0, v___x_1281_);
v___x_1316_ = v___x_1273_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v_a_1264_ = v___x_1316_;
goto v___jp_1263_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_del_object(v___x_1273_);
lean_dec(v_snd_1271_);
lean_dec(v_fst_1270_);
lean_dec(v_a_1258_);
v_a_1318_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1276_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1276_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
v___jp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_add(v_a_1258_, v___x_1265_);
lean_dec(v_a_1258_);
v_a_1258_ = v___x_1266_;
v_b_1259_ = v_a_1264_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1256_ = stack[0].m_obj;
lean_object* v_usedInstIdxs_1257_ = stack[1].m_obj;
lean_object* v_a_1258_ = stack[2].m_obj;
lean_object* v_b_1259_ = stack[3].m_obj;
lean_object* v___y_1260_ = stack[4].m_obj;
lean_object* v___y_1261_ = stack[5].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1256_, v_usedInstIdxs_1257_, v_a_1258_, v_b_1259_, v___y_1260_, v___y_1261_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___boxed(lean_object* v_upperBound_1328_, lean_object* v_usedInstIdxs_1329_, lean_object* v_a_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1328_, v_usedInstIdxs_1329_, v_a_1330_, v_b_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v_usedInstIdxs_1329_);
lean_dec(v_upperBound_1328_);
return v_res_1335_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_box(1);
v___x_1337_ = l_Lean_MessageData_ofFormat(v___x_1336_);
return v___x_1337_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2));
v___x_1342_ = l_Lean_MessageData_ofFormat(v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1344_) == 0)
{
return v_x_1343_;
}
else
{
lean_object* v_head_1345_; lean_object* v_tail_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1368_; 
v_head_1345_ = lean_ctor_get(v_x_1344_, 0);
v_tail_1346_ = lean_ctor_get(v_x_1344_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_x_1344_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1348_ = v_x_1344_;
v_isShared_1349_ = v_isSharedCheck_1368_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_tail_1346_);
lean_inc(v_head_1345_);
lean_dec(v_x_1344_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1368_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_before_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1366_; 
v_before_1350_ = lean_ctor_get(v_head_1345_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_head_1345_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v_head_1345_, 1);
lean_dec(v_unused_1367_);
v___x_1352_ = v_head_1345_;
v_isShared_1353_ = v_isSharedCheck_1366_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_before_1350_);
lean_dec(v_head_1345_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1366_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 7);
lean_ctor_set(v___x_1352_, 1, v___x_1354_);
lean_ctor_set(v___x_1352_, 0, v_x_1343_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_x_1343_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 7);
lean_ctor_set(v___x_1348_, 1, v___x_1357_);
lean_ctor_set(v___x_1348_, 0, v___x_1356_);
v___x_1359_ = v___x_1348_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = l_Lean_MessageData_ofSyntax(v_before_1350_);
v___x_1361_ = l_Lean_indentD(v___x_1360_);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1359_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v_x_1343_ = v___x_1362_;
v_x_1344_ = v_tail_1346_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_1369_, lean_object* v_opt_1370_){
_start:
{
lean_object* v_name_1371_; lean_object* v_defValue_1372_; lean_object* v_map_1373_; lean_object* v___x_1374_; 
v_name_1371_ = lean_ctor_get(v_opt_1370_, 0);
v_defValue_1372_ = lean_ctor_get(v_opt_1370_, 1);
v_map_1373_ = lean_ctor_get(v_opts_1369_, 0);
v___x_1374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1373_, v_name_1371_);
if (lean_obj_tag(v___x_1374_) == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_unbox(v_defValue_1372_);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; 
v_val_1376_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1374_, 1);
if (lean_obj_tag(v_val_1376_) == 1)
{
uint8_t v_v_1377_; 
v_v_1377_ = lean_ctor_get_uint8(v_val_1376_, 0);
lean_dec_ref_known(v_val_1376_, 0);
return v_v_1377_;
}
else
{
uint8_t v___x_1378_; 
lean_dec(v_val_1376_);
v___x_1378_ = lean_unbox(v_defValue_1372_);
return v___x_1378_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1369_ = stack[0].m_obj;
lean_object* v_opt_1370_ = stack[1].m_obj;
uint8_t v_res_1379_;
v_res_1379_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_1369_, v_opt_1370_);
stack->m_num = v_res_1379_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_1380_, lean_object* v_opt_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_1380_, v_opt_1381_);
lean_dec_ref(v_opt_1381_);
lean_dec_ref(v_opts_1380_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1388_ = l_Lean_MessageData_ofFormat(v___x_1387_);
return v___x_1388_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_1389_, lean_object* v_macroStack_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1391_);
v___x_1394_ = l_Lean_Elab_pp_macroStack;
v___x_1395_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v___x_1393_, v___x_1394_);
lean_dec_ref(v___x_1393_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec(v_macroStack_1390_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_msgData_1389_);
return v___x_1396_;
}
else
{
if (lean_obj_tag(v_macroStack_1390_) == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_msgData_1389_);
return v___x_1397_;
}
else
{
lean_object* v_head_1398_; lean_object* v_after_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1414_; 
v_head_1398_ = lean_ctor_get(v_macroStack_1390_, 0);
lean_inc(v_head_1398_);
v_after_1399_ = lean_ctor_get(v_head_1398_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_head_1398_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_head_1398_, 0);
lean_dec(v_unused_1415_);
v___x_1401_ = v_head_1398_;
v_isShared_1402_ = v_isSharedCheck_1414_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_after_1399_);
lean_dec(v_head_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1414_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 7);
lean_ctor_set(v___x_1401_, 1, v___x_1403_);
lean_ctor_set(v___x_1401_, 0, v_msgData_1389_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_msgData_1389_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_msgData_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1406_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_MessageData_ofSyntax(v_after_1399_);
v___x_1409_ = l_Lean_indentD(v___x_1408_);
v_msgData_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1410_, 0, v___x_1407_);
lean_ctor_set(v_msgData_1410_, 1, v___x_1409_);
v___x_1411_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_1410_, v_macroStack_1390_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1389_ = stack[0].m_obj;
lean_object* v_macroStack_1390_ = stack[1].m_obj;
lean_object* v___y_1391_ = stack[2].m_obj;
lean_object* v_res_1416_;
v_res_1416_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1389_, v_macroStack_1390_, v___y_1391_);
stack->m_obj
 = v_res_1416_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1417_, lean_object* v_macroStack_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1417_, v_macroStack_1418_, v___y_1419_);
lean_dec_ref(v___y_1419_);
return v_res_1421_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_ref_1430_; lean_object* v_macroStack_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_ref_1430_ = lean_ctor_get(v___y_1427_, 2);
v_macroStack_1431_ = lean_ctor_get(v___y_1423_, 1);
v___x_1432_ = l_Lean_Elab_getBetterRef(v_ref_1430_, v_macroStack_1431_);
v___x_1433_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1422_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
lean_inc(v_macroStack_1431_);
v___x_1435_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_a_1434_, v_macroStack_1431_, v___y_1427_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1432_);
lean_ctor_set(v___x_1440_, 1, v_a_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 1);
lean_ctor_set(v___x_1438_, 0, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1422_ = stack[0].m_obj;
lean_object* v___y_1423_ = stack[1].m_obj;
lean_object* v___y_1424_ = stack[2].m_obj;
lean_object* v___y_1425_ = stack[3].m_obj;
lean_object* v___y_1426_ = stack[4].m_obj;
lean_object* v___y_1427_ = stack[5].m_obj;
lean_object* v___y_1428_ = stack[6].m_obj;
lean_object* v_res_1445_;
v_res_1445_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
stack->m_obj
 = v_res_1445_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1454_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v_env_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_st_ref_get(v___y_1467_);
v_env_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc_ref(v_env_1470_);
lean_dec(v___x_1469_);
lean_inc(v_constName_1461_);
v___x_1471_ = l_Lean_isInductiveCore_x3f(v_env_1470_, v_constName_1461_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1472_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_1473_ = 0;
v___x_1474_ = l_Lean_MessageData_ofConstName(v_constName_1461_, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1472_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_1477_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1478_;
}
else
{
lean_object* v_val_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_constName_1461_);
v_val_1479_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1471_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_val_1479_);
lean_dec(v___x_1471_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 0);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_val_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1461_ = stack[0].m_obj;
lean_object* v___y_1462_ = stack[1].m_obj;
lean_object* v___y_1463_ = stack[2].m_obj;
lean_object* v___y_1464_ = stack[3].m_obj;
lean_object* v___y_1465_ = stack[4].m_obj;
lean_object* v___y_1466_ = stack[5].m_obj;
lean_object* v___y_1467_ = stack[6].m_obj;
lean_object* v_res_1487_;
v_res_1487_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_constName_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
stack->m_obj
 = v_res_1487_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___boxed(lean_object* v_constName_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_constName_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1496_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(size_t v_sz_1497_, size_t v_i_1498_, lean_object* v_bs_1499_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_lt(v_i_1498_, v_sz_1497_);
if (v___x_1500_ == 0)
{
return v_bs_1499_;
}
else
{
lean_object* v_v_1501_; lean_object* v___x_1502_; lean_object* v_bs_x27_1503_; size_t v___x_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v_v_1501_ = lean_array_uget(v_bs_1499_, v_i_1498_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v_bs_x27_1503_ = lean_array_uset(v_bs_1499_, v_i_1498_, v___x_1502_);
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_add(v_i_1498_, v___x_1504_);
v___x_1506_ = lean_array_uset(v_bs_x27_1503_, v_i_1498_, v_v_1501_);
v_i_1498_ = v___x_1505_;
v_bs_1499_ = v___x_1506_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1497_ = stack[0].m_num;
size_t v_i_1498_ = stack[1].m_num;
lean_object* v_bs_1499_ = stack[2].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_1497_, v_i_1498_, v_bs_1499_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0___boxed(lean_object* v_sz_1509_, lean_object* v_i_1510_, lean_object* v_bs_1511_){
_start:
{
size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1509_);
lean_dec(v_sz_1509_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_boxed_1512_, v_i_boxed_1513_, v_bs_1511_);
return v_res_1514_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(lean_object* v_inductiveTypeName_1592_, lean_object* v_instId_1593_, lean_object* v_usedInstIdxs_1594_, lean_object* v_auxFunId_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; 
lean_inc(v_inductiveTypeName_1592_);
v___x_1603_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_1592_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v_numParams_1605_; lean_object* v_numIndices_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v_numParams_1605_ = lean_ctor_get(v_a_1604_, 1);
lean_inc(v_numParams_1605_);
v_numIndices_1606_ = lean_ctor_get(v_a_1604_, 2);
lean_inc(v_numIndices_1606_);
lean_dec(v_a_1604_);
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = lean_nat_add(v_numParams_1605_, v_numIndices_1606_);
lean_dec(v_numIndices_1606_);
lean_dec(v_numParams_1605_);
v___x_1609_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1));
v___x_1610_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v___x_1608_, v_usedInstIdxs_1594_, v___x_1607_, v___x_1609_, v_a_1600_, v_a_1601_);
lean_dec(v___x_1608_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1688_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1688_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1688_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_fst_1615_; lean_object* v_snd_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1687_; 
v_fst_1615_ = lean_ctor_get(v_a_1611_, 0);
v_snd_1616_ = lean_ctor_get(v_a_1611_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_a_1611_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1618_ = v_a_1611_;
v_isShared_1619_ = v_isSharedCheck_1687_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_snd_1616_);
lean_inc(v_fst_1615_);
lean_dec(v_a_1611_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1687_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v_toCold_1620_; lean_object* v_ref_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v_toCold_1620_ = lean_ctor_get(v_a_1600_, 0);
v_ref_1621_ = lean_ctor_get(v_a_1600_, 2);
v___x_1622_ = 0;
v___x_1623_ = l_Lean_SourceInfo_fromRef(v_ref_1621_, v___x_1622_);
v___x_1624_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1625_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3));
v___x_1626_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4));
lean_inc(v___x_1623_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 2);
lean_ctor_set(v___x_1618_, 1, v___x_1626_);
lean_ctor_set(v___x_1618_, 0, v___x_1623_);
v___x_1628_ = v___x_1618_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v_quotContext_1631_; lean_object* v_currMacroScope_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; size_t v_sz_1651_; size_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1629_ = l_Lean_mkCIdent(v_inductiveTypeName_1592_);
lean_inc_n(v___x_1623_, 24);
v___x_1630_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1625_, v___x_1628_, v___x_1629_);
v_quotContext_1631_ = lean_ctor_get(v_toCold_1620_, 8);
v_currMacroScope_1632_ = lean_ctor_get(v_toCold_1620_, 9);
v___x_1633_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1634_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1635_ = l_Array_append___redArg(v___x_1634_, v_fst_1615_);
lean_dec(v_fst_1615_);
v___x_1636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1623_);
lean_ctor_set(v___x_1636_, 1, v___x_1633_);
lean_ctor_set(v___x_1636_, 2, v___x_1635_);
v___x_1637_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1624_, v___x_1630_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7));
v___x_1639_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9));
v___x_1640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1623_);
lean_ctor_set(v___x_1640_, 1, v___x_1633_);
lean_ctor_set(v___x_1640_, 2, v___x_1634_);
lean_inc_ref_n(v___x_1640_, 12);
v___x_1641_ = l_Lean_Syntax_node7(v___x_1623_, v___x_1639_, v___x_1640_, v___x_1640_, v___x_1640_, v___x_1640_, v___x_1640_, v___x_1640_, v___x_1640_);
v___x_1642_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10));
v___x_1643_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11));
v___x_1644_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13));
v___x_1645_ = l_Lean_Syntax_node1(v___x_1623_, v___x_1644_, v___x_1640_);
v___x_1646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1623_);
lean_ctor_set(v___x_1646_, 1, v___x_1642_);
v___x_1647_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15));
v___x_1648_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1647_, v_instId_1593_, v___x_1640_);
v___x_1649_ = l_Lean_Syntax_node1(v___x_1623_, v___x_1633_, v___x_1648_);
v___x_1650_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17));
v_sz_1651_ = lean_array_size(v_snd_1616_);
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_1651_, v___x_1652_, v_snd_1616_);
v___x_1654_ = l_Array_append___redArg(v___x_1634_, v___x_1653_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1623_);
lean_ctor_set(v___x_1655_, 1, v___x_1633_);
lean_ctor_set(v___x_1655_, 2, v___x_1654_);
v___x_1656_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19));
v___x_1657_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20));
v___x_1658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1623_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1660_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1632_);
lean_inc(v_quotContext_1631_);
v___x_1661_ = l_Lean_addMacroScope(v_quotContext_1631_, v___x_1660_, v_currMacroScope_1632_);
v___x_1662_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1663_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1623_);
lean_ctor_set(v___x_1663_, 1, v___x_1659_);
lean_ctor_set(v___x_1663_, 2, v___x_1661_);
lean_ctor_set(v___x_1663_, 3, v___x_1662_);
v___x_1664_ = l_Lean_Syntax_node1(v___x_1623_, v___x_1633_, v___x_1637_);
v___x_1665_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1624_, v___x_1663_, v___x_1664_);
v___x_1666_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1656_, v___x_1658_, v___x_1665_);
v___x_1667_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1650_, v___x_1655_, v___x_1666_);
v___x_1668_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22));
v___x_1669_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23));
v___x_1670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1623_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25));
v___x_1672_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26));
v___x_1673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1623_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_Syntax_node1(v___x_1623_, v___x_1633_, v_auxFunId_1595_);
v___x_1675_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27));
v___x_1676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1623_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_Syntax_node3(v___x_1623_, v___x_1671_, v___x_1673_, v___x_1674_, v___x_1676_);
v___x_1678_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30));
v___x_1679_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1678_, v___x_1640_, v___x_1640_);
v___x_1680_ = l_Lean_Syntax_node4(v___x_1623_, v___x_1668_, v___x_1670_, v___x_1677_, v___x_1679_, v___x_1640_);
v___x_1681_ = l_Lean_Syntax_node6(v___x_1623_, v___x_1643_, v___x_1645_, v___x_1646_, v___x_1640_, v___x_1649_, v___x_1667_, v___x_1680_);
v___x_1682_ = l_Lean_Syntax_node2(v___x_1623_, v___x_1638_, v___x_1641_, v___x_1681_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1682_);
v___x_1684_ = v___x_1613_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_auxFunId_1595_);
lean_dec(v_instId_1593_);
lean_dec(v_inductiveTypeName_1592_);
v_a_1689_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1610_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1610_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_auxFunId_1595_);
lean_dec(v_instId_1593_);
lean_dec(v_inductiveTypeName_1592_);
v_a_1697_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1603_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1603_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_inductiveTypeName_1592_ = stack[0].m_obj;
lean_object* v_instId_1593_ = stack[1].m_obj;
lean_object* v_usedInstIdxs_1594_ = stack[2].m_obj;
lean_object* v_auxFunId_1595_ = stack[3].m_obj;
lean_object* v_a_1596_ = stack[4].m_obj;
lean_object* v_a_1597_ = stack[5].m_obj;
lean_object* v_a_1598_ = stack[6].m_obj;
lean_object* v_a_1599_ = stack[7].m_obj;
lean_object* v_a_1600_ = stack[8].m_obj;
lean_object* v_a_1601_ = stack[9].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_1592_, v_instId_1593_, v_usedInstIdxs_1594_, v_auxFunId_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___boxed(lean_object* v_inductiveTypeName_1706_, lean_object* v_instId_1707_, lean_object* v_usedInstIdxs_1708_, lean_object* v_auxFunId_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_1706_, v_instId_1707_, v_usedInstIdxs_1708_, v_auxFunId_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_usedInstIdxs_1708_);
return v_res_1717_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(lean_object* v_upperBound_1718_, lean_object* v_usedInstIdxs_1719_, lean_object* v_inst_1720_, lean_object* v_R_1721_, lean_object* v_a_1722_, lean_object* v_b_1723_, lean_object* v_c_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1718_, v_usedInstIdxs_1719_, v_a_1722_, v_b_1723_, v___y_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1718_ = stack[0].m_obj;
lean_object* v_usedInstIdxs_1719_ = stack[1].m_obj;
lean_object* v_a_1722_ = stack[4].m_obj;
lean_object* v_b_1723_ = stack[5].m_obj;
lean_object* v___y_1725_ = stack[7].m_obj;
lean_object* v___y_1726_ = stack[8].m_obj;
lean_object* v___y_1727_ = stack[9].m_obj;
lean_object* v___y_1728_ = stack[10].m_obj;
lean_object* v___y_1729_ = stack[11].m_obj;
lean_object* v___y_1730_ = stack[12].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(v_upperBound_1718_, v_usedInstIdxs_1719_, lean_box(0), lean_box(0), v_a_1722_, v_b_1723_, lean_box(0), v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___boxed(lean_object* v_upperBound_1734_, lean_object* v_usedInstIdxs_1735_, lean_object* v_inst_1736_, lean_object* v_R_1737_, lean_object* v_a_1738_, lean_object* v_b_1739_, lean_object* v_c_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(v_upperBound_1734_, v_usedInstIdxs_1735_, v_inst_1736_, v_R_1737_, v_a_1738_, v_b_1739_, v_c_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v_usedInstIdxs_1735_);
lean_dec(v_upperBound_1734_);
return v_res_1748_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_object* v_00_u03b1_1749_, lean_object* v_msg_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1750_ = stack[1].m_obj;
lean_object* v___y_1751_ = stack[2].m_obj;
lean_object* v___y_1752_ = stack[3].m_obj;
lean_object* v___y_1753_ = stack[4].m_obj;
lean_object* v___y_1754_ = stack[5].m_obj;
lean_object* v___y_1755_ = stack[6].m_obj;
lean_object* v___y_1756_ = stack[7].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_box(0), v_msg_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1760_, lean_object* v_msg_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(v_00_u03b1_1760_, v_msg_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1769_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(lean_object* v_msgData_1770_, lean_object* v_macroStack_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1770_, v_macroStack_1771_, v___y_1776_);
return v___x_1779_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1770_ = stack[0].m_obj;
lean_object* v_macroStack_1771_ = stack[1].m_obj;
lean_object* v___y_1772_ = stack[2].m_obj;
lean_object* v___y_1773_ = stack[3].m_obj;
lean_object* v___y_1774_ = stack[4].m_obj;
lean_object* v___y_1775_ = stack[5].m_obj;
lean_object* v___y_1776_ = stack[6].m_obj;
lean_object* v___y_1777_ = stack[7].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(v_msgData_1770_, v_macroStack_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
stack->m_obj
 = v_res_1780_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1781_, lean_object* v_macroStack_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(v_msgData_1781_, v_macroStack_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1790_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_unsigned_to_nat(32u);
v___x_1792_ = lean_mk_empty_array_with_capacity(v___x_1791_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1794_ = ((size_t)5ULL);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_unsigned_to_nat(32u);
v___x_1797_ = lean_mk_empty_array_with_capacity(v___x_1796_);
v___x_1798_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0);
v___x_1799_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1797_);
lean_ctor_set(v___x_1799_, 2, v___x_1795_);
lean_ctor_set(v___x_1799_, 3, v___x_1795_);
lean_ctor_set_usize(v___x_1799_, 4, v___x_1794_);
return v___x_1799_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; lean_object* v_traceState_1803_; lean_object* v_traces_1804_; lean_object* v___x_1805_; lean_object* v_traceState_1806_; lean_object* v_env_1807_; lean_object* v_nextMacroScope_1808_; lean_object* v_ngen_1809_; lean_object* v_auxDeclNGen_1810_; lean_object* v_cache_1811_; lean_object* v_recordedDeps_1812_; lean_object* v_messages_1813_; lean_object* v_infoState_1814_; lean_object* v_snapshotTasks_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1834_; 
v___x_1802_ = lean_st_ref_get(v___y_1800_);
v_traceState_1803_ = lean_ctor_get(v___x_1802_, 4);
lean_inc_ref(v_traceState_1803_);
lean_dec(v___x_1802_);
v_traces_1804_ = lean_ctor_get(v_traceState_1803_, 0);
lean_inc_ref(v_traces_1804_);
lean_dec_ref(v_traceState_1803_);
v___x_1805_ = lean_st_ref_take(v___y_1800_);
v_traceState_1806_ = lean_ctor_get(v___x_1805_, 4);
v_env_1807_ = lean_ctor_get(v___x_1805_, 0);
v_nextMacroScope_1808_ = lean_ctor_get(v___x_1805_, 1);
v_ngen_1809_ = lean_ctor_get(v___x_1805_, 2);
v_auxDeclNGen_1810_ = lean_ctor_get(v___x_1805_, 3);
v_cache_1811_ = lean_ctor_get(v___x_1805_, 5);
v_recordedDeps_1812_ = lean_ctor_get(v___x_1805_, 6);
v_messages_1813_ = lean_ctor_get(v___x_1805_, 7);
v_infoState_1814_ = lean_ctor_get(v___x_1805_, 8);
v_snapshotTasks_1815_ = lean_ctor_get(v___x_1805_, 9);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1817_ = v___x_1805_;
v_isShared_1818_ = v_isSharedCheck_1834_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_snapshotTasks_1815_);
lean_inc(v_infoState_1814_);
lean_inc(v_messages_1813_);
lean_inc(v_recordedDeps_1812_);
lean_inc(v_cache_1811_);
lean_inc(v_traceState_1806_);
lean_inc(v_auxDeclNGen_1810_);
lean_inc(v_ngen_1809_);
lean_inc(v_nextMacroScope_1808_);
lean_inc(v_env_1807_);
lean_dec(v___x_1805_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1834_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
uint64_t v_tid_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1832_; 
v_tid_1819_ = lean_ctor_get_uint64(v_traceState_1806_, sizeof(void*)*1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_traceState_1806_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v_traceState_1806_, 0);
lean_dec(v_unused_1833_);
v___x_1821_ = v_traceState_1806_;
v_isShared_1822_ = v_isSharedCheck_1832_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v_traceState_1806_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1832_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1823_);
lean_ctor_set_uint64(v_reuseFailAlloc_1831_, sizeof(void*)*1, v_tid_1819_);
v___x_1825_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1827_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v___x_1825_);
v___x_1827_ = v___x_1817_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_env_1807_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_nextMacroScope_1808_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_ngen_1809_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v_auxDeclNGen_1810_);
lean_ctor_set(v_reuseFailAlloc_1830_, 4, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1830_, 5, v_cache_1811_);
lean_ctor_set(v_reuseFailAlloc_1830_, 6, v_recordedDeps_1812_);
lean_ctor_set(v_reuseFailAlloc_1830_, 7, v_messages_1813_);
lean_ctor_set(v_reuseFailAlloc_1830_, 8, v_infoState_1814_);
lean_ctor_set(v_reuseFailAlloc_1830_, 9, v_snapshotTasks_1815_);
v___x_1827_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_st_ref_put(v___y_1800_, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_traces_1804_);
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1800_ = stack[0].m_obj;
lean_object* v_res_1835_;
v_res_1835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1800_);
stack->m_obj
 = v_res_1835_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___boxed(lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1836_);
lean_dec(v___y_1836_);
return v_res_1838_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1839_ = stack[0].m_obj;
lean_object* v___y_1840_ = stack[1].m_obj;
lean_object* v___y_1841_ = stack[2].m_obj;
lean_object* v___y_1842_ = stack[3].m_obj;
lean_object* v___y_1843_ = stack[4].m_obj;
lean_object* v___y_1844_ = stack[5].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v_res_1855_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
v___x_1864_ = lean_apply_7(v_x_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, lean_box(0));
return v___x_1864_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1856_ = stack[0].m_obj;
lean_object* v___y_1857_ = stack[1].m_obj;
lean_object* v___y_1858_ = stack[2].m_obj;
lean_object* v___y_1859_ = stack[3].m_obj;
lean_object* v___y_1860_ = stack[4].m_obj;
lean_object* v___y_1861_ = stack[5].m_obj;
lean_object* v___y_1862_ = stack[6].m_obj;
lean_object* v_res_1865_;
v_res_1865_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(v_x_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
stack->m_obj
 = v_res_1865_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(v_x_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1874_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object* v_mvarId_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___f_1884_; lean_object* v___x_1885_; 
lean_inc(v___y_1878_);
lean_inc_ref(v___y_1877_);
v___f_1884_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1884_, 0, v_x_1876_);
lean_closure_set(v___f_1884_, 1, v___y_1877_);
lean_closure_set(v___f_1884_, 2, v___y_1878_);
v___x_1885_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1875_, v___f_1884_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1885_) == 0)
{
return v___x_1885_;
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1875_ = stack[0].m_obj;
lean_object* v_x_1876_ = stack[1].m_obj;
lean_object* v___y_1877_ = stack[2].m_obj;
lean_object* v___y_1878_ = stack[3].m_obj;
lean_object* v___y_1879_ = stack[4].m_obj;
lean_object* v___y_1880_ = stack[5].m_obj;
lean_object* v___y_1881_ = stack[6].m_obj;
lean_object* v___y_1882_ = stack[7].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1875_, v_x_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object* v_mvarId_1895_, lean_object* v_x_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1895_, v_x_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1904_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object* v_00_u03b1_1905_, lean_object* v_mvarId_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1906_, v_x_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1906_ = stack[1].m_obj;
lean_object* v_x_1907_ = stack[2].m_obj;
lean_object* v___y_1908_ = stack[3].m_obj;
lean_object* v___y_1909_ = stack[4].m_obj;
lean_object* v___y_1910_ = stack[5].m_obj;
lean_object* v___y_1911_ = stack[6].m_obj;
lean_object* v___y_1912_ = stack[7].m_obj;
lean_object* v___y_1913_ = stack[8].m_obj;
lean_object* v_res_1916_;
v_res_1916_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_box(0), v_mvarId_1906_, v_x_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
stack->m_obj
 = v_res_1916_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object* v_00_u03b1_1917_, lean_object* v_mvarId_1918_, lean_object* v_x_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(v_00_u03b1_1917_, v_mvarId_1918_, v_x_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0));
v___x_1930_ = l_Lean_stringToMessageData(v___x_1929_);
return v___x_1930_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object* v_a_1931_, lean_object* v_x_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1940_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1);
v___x_1941_ = lean_unsigned_to_nat(30u);
v___x_1942_ = l_Lean_inlineExprTrailing(v_a_1931_, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1940_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1931_ = stack[0].m_obj;
lean_object* v_x_1932_ = stack[1].m_obj;
lean_object* v___y_1933_ = stack[2].m_obj;
lean_object* v___y_1934_ = stack[3].m_obj;
lean_object* v___y_1935_ = stack[4].m_obj;
lean_object* v___y_1936_ = stack[5].m_obj;
lean_object* v___y_1937_ = stack[6].m_obj;
lean_object* v___y_1938_ = stack[7].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(v_a_1931_, v_x_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object* v_a_1946_, lean_object* v_x_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(v_a_1946_, v_x_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec_ref(v_x_1947_);
return v_res_1955_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(lean_object* v_e_1956_){
_start:
{
if (lean_obj_tag(v_e_1956_) == 0)
{
uint8_t v___x_1957_; 
v___x_1957_ = 2;
return v___x_1957_;
}
else
{
uint8_t v___x_1958_; 
v___x_1958_ = 0;
return v___x_1958_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1956_ = stack[0].m_obj;
uint8_t v_res_1959_;
v_res_1959_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_e_1956_);
stack->m_num = v_res_1959_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___boxed(lean_object* v_e_1960_){
_start:
{
uint8_t v_res_1961_; lean_object* v_r_1962_; 
v_res_1961_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_e_1960_);
lean_dec_ref(v_e_1960_);
v_r_1962_ = lean_box(v_res_1961_);
return v_r_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object* v_opts_1963_, lean_object* v_opt_1964_){
_start:
{
lean_object* v_name_1965_; lean_object* v_defValue_1966_; lean_object* v_map_1967_; lean_object* v___x_1968_; 
v_name_1965_ = lean_ctor_get(v_opt_1964_, 0);
v_defValue_1966_ = lean_ctor_get(v_opt_1964_, 1);
v_map_1967_ = lean_ctor_get(v_opts_1963_, 0);
v___x_1968_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1967_, v_name_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_inc(v_defValue_1966_);
return v_defValue_1966_;
}
else
{
lean_object* v_val_1969_; 
v_val_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v___x_1968_, 1);
if (lean_obj_tag(v_val_1969_) == 3)
{
lean_object* v_v_1970_; 
v_v_1970_ = lean_ctor_get(v_val_1969_, 0);
lean_inc(v_v_1970_);
lean_dec_ref_known(v_val_1969_, 1);
return v_v_1970_;
}
else
{
lean_dec(v_val_1969_);
lean_inc(v_defValue_1966_);
return v_defValue_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___boxed(lean_object* v_opts_1971_, lean_object* v_opt_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_1971_, v_opt_1972_);
lean_dec_ref(v_opt_1972_);
lean_dec_ref(v_opts_1971_);
return v_res_1973_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object* v_x_1974_){
_start:
{
if (lean_obj_tag(v_x_1974_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
v_a_1976_ = lean_ctor_get(v_x_1974_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_x_1974_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v_x_1974_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v_x_1974_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 1);
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
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
v_a_1984_ = lean_ctor_get(v_x_1974_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_x_1974_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v_x_1974_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v_x_1974_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 0);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1974_ = stack[0].m_obj;
lean_object* v_res_1992_;
v_res_1992_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_1974_);
stack->m_obj
 = v_res_1992_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg___boxed(lean_object* v_x_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_1993_);
return v_res_1995_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_bs_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
if (v___x_1999_ == 0)
{
return v_bs_1998_;
}
else
{
lean_object* v_v_2000_; lean_object* v_msg_2001_; lean_object* v___x_2002_; lean_object* v_bs_x27_2003_; size_t v___x_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v_v_2000_ = lean_array_uget_borrowed(v_bs_1998_, v_i_1997_);
v_msg_2001_ = lean_ctor_get(v_v_2000_, 1);
lean_inc_ref(v_msg_2001_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v_bs_x27_2003_ = lean_array_uset(v_bs_1998_, v_i_1997_, v___x_2002_);
v___x_2004_ = ((size_t)1ULL);
v___x_2005_ = lean_usize_add(v_i_1997_, v___x_2004_);
v___x_2006_ = lean_array_uset(v_bs_x27_2003_, v_i_1997_, v_msg_2001_);
v_i_1997_ = v___x_2005_;
v_bs_1998_ = v___x_2006_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1996_ = stack[0].m_num;
size_t v_i_1997_ = stack[1].m_num;
lean_object* v_bs_1998_ = stack[2].m_obj;
lean_object* v_res_2008_;
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_1996_, v_i_1997_, v_bs_1998_);
stack->m_obj
 = v_res_2008_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_2009_, lean_object* v_i_2010_, lean_object* v_bs_2011_){
_start:
{
size_t v_sz_boxed_2012_; size_t v_i_boxed_2013_; lean_object* v_res_2014_; 
v_sz_boxed_2012_ = lean_unbox_usize(v_sz_2009_);
lean_dec(v_sz_2009_);
v_i_boxed_2013_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_boxed_2012_, v_i_boxed_2013_, v_bs_2011_);
return v_res_2014_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(lean_object* v_oldTraces_2015_, lean_object* v_data_2016_, lean_object* v_ref_2017_, lean_object* v_msg_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_toCold_2024_; lean_object* v_currRecDepth_2025_; lean_object* v_ref_2026_; uint16_t v_optionFlags_2027_; uint8_t v_suppressElabErrors_2028_; uint8_t v_isRecordingDeps_2029_; lean_object* v_ref_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v_traceState_2033_; lean_object* v_traces_2034_; lean_object* v___x_2035_; size_t v_sz_2036_; size_t v___x_2037_; lean_object* v___x_2038_; lean_object* v_msg_2039_; lean_object* v___x_2040_; lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2079_; 
v_toCold_2024_ = lean_ctor_get(v___y_2021_, 0);
v_currRecDepth_2025_ = lean_ctor_get(v___y_2021_, 1);
v_ref_2026_ = lean_ctor_get(v___y_2021_, 2);
v_optionFlags_2027_ = lean_ctor_get_uint16(v___y_2021_, sizeof(void*)*3);
v_suppressElabErrors_2028_ = lean_ctor_get_uint8(v___y_2021_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2029_ = lean_ctor_get_uint8(v___y_2021_, sizeof(void*)*3 + 3);
v_ref_2030_ = l_Lean_replaceRef(v_ref_2017_, v_ref_2026_);
lean_inc(v_currRecDepth_2025_);
lean_inc_ref(v_toCold_2024_);
v___x_2031_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2031_, 0, v_toCold_2024_);
lean_ctor_set(v___x_2031_, 1, v_currRecDepth_2025_);
lean_ctor_set(v___x_2031_, 2, v_ref_2030_);
lean_ctor_set_uint16(v___x_2031_, sizeof(void*)*3, v_optionFlags_2027_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*3 + 2, v_suppressElabErrors_2028_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*3 + 3, v_isRecordingDeps_2029_);
v___x_2032_ = lean_st_ref_get(v___y_2022_);
v_traceState_2033_ = lean_ctor_get(v___x_2032_, 4);
lean_inc_ref(v_traceState_2033_);
lean_dec(v___x_2032_);
v_traces_2034_ = lean_ctor_get(v_traceState_2033_, 0);
lean_inc_ref(v_traces_2034_);
lean_dec_ref(v_traceState_2033_);
v___x_2035_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2034_);
lean_dec_ref(v_traces_2034_);
v_sz_2036_ = lean_array_size(v___x_2035_);
v___x_2037_ = ((size_t)0ULL);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_2036_, v___x_2037_, v___x_2035_);
v_msg_2039_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2039_, 0, v_data_2016_);
lean_ctor_set(v_msg_2039_, 1, v_msg_2018_);
lean_ctor_set(v_msg_2039_, 2, v___x_2038_);
v___x_2040_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_2039_, v___y_2019_, v___y_2020_, v___x_2031_, v___y_2022_);
lean_dec_ref_known(v___x_2031_, 3);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2079_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2079_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v_traceState_2046_; lean_object* v_env_2047_; lean_object* v_nextMacroScope_2048_; lean_object* v_ngen_2049_; lean_object* v_auxDeclNGen_2050_; lean_object* v_cache_2051_; lean_object* v_recordedDeps_2052_; lean_object* v_messages_2053_; lean_object* v_infoState_2054_; lean_object* v_snapshotTasks_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2078_; 
v___x_2045_ = lean_st_ref_take(v___y_2022_);
v_traceState_2046_ = lean_ctor_get(v___x_2045_, 4);
v_env_2047_ = lean_ctor_get(v___x_2045_, 0);
v_nextMacroScope_2048_ = lean_ctor_get(v___x_2045_, 1);
v_ngen_2049_ = lean_ctor_get(v___x_2045_, 2);
v_auxDeclNGen_2050_ = lean_ctor_get(v___x_2045_, 3);
v_cache_2051_ = lean_ctor_get(v___x_2045_, 5);
v_recordedDeps_2052_ = lean_ctor_get(v___x_2045_, 6);
v_messages_2053_ = lean_ctor_get(v___x_2045_, 7);
v_infoState_2054_ = lean_ctor_get(v___x_2045_, 8);
v_snapshotTasks_2055_ = lean_ctor_get(v___x_2045_, 9);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2057_ = v___x_2045_;
v_isShared_2058_ = v_isSharedCheck_2078_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snapshotTasks_2055_);
lean_inc(v_infoState_2054_);
lean_inc(v_messages_2053_);
lean_inc(v_recordedDeps_2052_);
lean_inc(v_cache_2051_);
lean_inc(v_traceState_2046_);
lean_inc(v_auxDeclNGen_2050_);
lean_inc(v_ngen_2049_);
lean_inc(v_nextMacroScope_2048_);
lean_inc(v_env_2047_);
lean_dec(v___x_2045_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2078_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
uint64_t v_tid_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2076_; 
v_tid_2059_ = lean_ctor_get_uint64(v_traceState_2046_, sizeof(void*)*1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_traceState_2046_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_traceState_2046_, 0);
lean_dec(v_unused_2077_);
v___x_2061_ = v_traceState_2046_;
v_isShared_2062_ = v_isSharedCheck_2076_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_traceState_2046_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2076_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_ref_2017_);
lean_ctor_set(v___x_2064_, 1, v_a_2041_);
v___x_2065_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2015_, v___x_2064_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2065_);
v___x_2067_ = v___x_2061_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2065_);
lean_ctor_set_uint64(v_reuseFailAlloc_2075_, sizeof(void*)*1, v_tid_2059_);
v___x_2067_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 4, v___x_2067_);
v___x_2069_ = v___x_2057_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_env_2047_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_nextMacroScope_2048_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_ngen_2049_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_auxDeclNGen_2050_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v_cache_2051_);
lean_ctor_set(v_reuseFailAlloc_2074_, 6, v_recordedDeps_2052_);
lean_ctor_set(v_reuseFailAlloc_2074_, 7, v_messages_2053_);
lean_ctor_set(v_reuseFailAlloc_2074_, 8, v_infoState_2054_);
lean_ctor_set(v_reuseFailAlloc_2074_, 9, v_snapshotTasks_2055_);
v___x_2069_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_st_ref_put(v___y_2022_, v___x_2069_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2063_);
v___x_2072_ = v___x_2043_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2063_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_2015_ = stack[0].m_obj;
lean_object* v_data_2016_ = stack[1].m_obj;
lean_object* v_ref_2017_ = stack[2].m_obj;
lean_object* v_msg_2018_ = stack[3].m_obj;
lean_object* v___y_2019_ = stack[4].m_obj;
lean_object* v___y_2020_ = stack[5].m_obj;
lean_object* v___y_2021_ = stack[6].m_obj;
lean_object* v___y_2022_ = stack[7].m_obj;
lean_object* v_res_2080_;
v_res_2080_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2015_, v_data_2016_, v_ref_2017_, v_msg_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
stack->m_obj
 = v_res_2080_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg___boxed(lean_object* v_oldTraces_2081_, lean_object* v_data_2082_, lean_object* v_ref_2083_, lean_object* v_msg_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2081_, v_data_2082_, v_ref_2083_, v_msg_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2090_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0));
v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
return v___x_2093_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2094_; double v___x_2095_; 
v___x_2094_ = lean_unsigned_to_nat(1000u);
v___x_2095_ = lean_float_of_nat(v___x_2094_);
return v___x_2095_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object* v_cls_2096_, uint8_t v_collapsed_2097_, lean_object* v_tag_2098_, lean_object* v_opts_2099_, uint8_t v_clsEnabled_2100_, lean_object* v_oldTraces_2101_, lean_object* v_msg_2102_, lean_object* v_resStartStop_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_fst_2111_; lean_object* v_snd_2112_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v_data_2116_; lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___y_2124_; lean_object* v_a_2125_; uint8_t v___y_2140_; double v___y_2172_; 
v_fst_2111_ = lean_ctor_get(v_resStartStop_2103_, 0);
lean_inc(v_fst_2111_);
v_snd_2112_ = lean_ctor_get(v_resStartStop_2103_, 1);
lean_inc(v_snd_2112_);
lean_dec_ref(v_resStartStop_2103_);
v_fst_2119_ = lean_ctor_get(v_snd_2112_, 0);
lean_inc(v_fst_2119_);
v_snd_2120_ = lean_ctor_get(v_snd_2112_, 1);
lean_inc(v_snd_2120_);
lean_dec(v_snd_2112_);
v___x_2121_ = l_Lean_trace_profiler;
v___x_2122_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2099_, v___x_2121_);
if (v___x_2122_ == 0)
{
v___y_2140_ = v___x_2122_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2178_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2099_, v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; double v___x_2181_; double v___x_2182_; double v___x_2183_; 
v___x_2179_ = l_Lean_trace_profiler_threshold;
v___x_2180_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2099_, v___x_2179_);
v___x_2181_ = lean_float_of_nat(v___x_2180_);
v___x_2182_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_2183_ = lean_float_div(v___x_2181_, v___x_2182_);
v___y_2172_ = v___x_2183_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; double v___x_2186_; 
v___x_2184_ = l_Lean_trace_profiler_threshold;
v___x_2185_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2099_, v___x_2184_);
v___x_2186_ = lean_float_of_nat(v___x_2185_);
v___y_2172_ = v___x_2186_;
goto v___jp_2171_;
}
}
v___jp_2113_:
{
lean_object* v___x_2117_; 
lean_inc(v___y_2114_);
v___x_2117_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2101_, v_data_2116_, v___y_2114_, v___y_2115_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref_known(v___x_2117_, 1);
v___x_2118_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2111_);
return v___x_2118_;
}
else
{
lean_dec(v_fst_2111_);
return v___x_2117_;
}
}
v___jp_2123_:
{
uint8_t v_result_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; double v___x_2129_; lean_object* v_data_2130_; 
v_result_2126_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_fst_2111_);
v___x_2127_ = lean_box(v_result_2126_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
v___x_2129_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2098_);
lean_inc_ref(v___x_2128_);
lean_inc(v_cls_2096_);
v_data_2130_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2130_, 0, v_cls_2096_);
lean_ctor_set(v_data_2130_, 1, v___x_2128_);
lean_ctor_set(v_data_2130_, 2, v_tag_2098_);
lean_ctor_set_float(v_data_2130_, sizeof(void*)*3, v___x_2129_);
lean_ctor_set_float(v_data_2130_, sizeof(void*)*3 + 8, v___x_2129_);
lean_ctor_set_uint8(v_data_2130_, sizeof(void*)*3 + 16, v_collapsed_2097_);
if (v___x_2122_ == 0)
{
lean_dec_ref_known(v___x_2128_, 1);
lean_dec(v_snd_2120_);
lean_dec(v_fst_2119_);
lean_dec_ref(v_tag_2098_);
lean_dec(v_cls_2096_);
v___y_2114_ = v___y_2124_;
v___y_2115_ = v_a_2125_;
v_data_2116_ = v_data_2130_;
goto v___jp_2113_;
}
else
{
lean_object* v_data_2131_; double v___x_2132_; double v___x_2133_; 
lean_dec_ref_known(v_data_2130_, 3);
v_data_2131_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2131_, 0, v_cls_2096_);
lean_ctor_set(v_data_2131_, 1, v___x_2128_);
lean_ctor_set(v_data_2131_, 2, v_tag_2098_);
v___x_2132_ = lean_unbox_float(v_fst_2119_);
lean_dec(v_fst_2119_);
lean_ctor_set_float(v_data_2131_, sizeof(void*)*3, v___x_2132_);
v___x_2133_ = lean_unbox_float(v_snd_2120_);
lean_dec(v_snd_2120_);
lean_ctor_set_float(v_data_2131_, sizeof(void*)*3 + 8, v___x_2133_);
lean_ctor_set_uint8(v_data_2131_, sizeof(void*)*3 + 16, v_collapsed_2097_);
v___y_2114_ = v___y_2124_;
v___y_2115_ = v_a_2125_;
v_data_2116_ = v_data_2131_;
goto v___jp_2113_;
}
}
v___jp_2134_:
{
lean_object* v_ref_2135_; lean_object* v___x_2136_; 
v_ref_2135_ = lean_ctor_get(v___y_2108_, 2);
lean_inc(v___y_2109_);
lean_inc_ref(v___y_2108_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___y_2105_);
lean_inc_ref(v___y_2104_);
lean_inc(v_fst_2111_);
v___x_2136_ = lean_apply_8(v_msg_2102_, v_fst_2111_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, lean_box(0));
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___y_2124_ = v_ref_2135_;
v_a_2125_ = v_a_2137_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2138_; 
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_2124_ = v_ref_2135_;
v_a_2125_ = v___x_2138_;
goto v___jp_2123_;
}
}
v___jp_2139_:
{
if (v_clsEnabled_2100_ == 0)
{
if (v___y_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v_traceState_2142_; lean_object* v_env_2143_; lean_object* v_nextMacroScope_2144_; lean_object* v_ngen_2145_; lean_object* v_auxDeclNGen_2146_; lean_object* v_cache_2147_; lean_object* v_recordedDeps_2148_; lean_object* v_messages_2149_; lean_object* v_infoState_2150_; lean_object* v_snapshotTasks_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_snd_2120_);
lean_dec(v_fst_2119_);
lean_dec_ref(v_msg_2102_);
lean_dec_ref(v_tag_2098_);
lean_dec(v_cls_2096_);
v___x_2141_ = lean_st_ref_take(v___y_2109_);
v_traceState_2142_ = lean_ctor_get(v___x_2141_, 4);
v_env_2143_ = lean_ctor_get(v___x_2141_, 0);
v_nextMacroScope_2144_ = lean_ctor_get(v___x_2141_, 1);
v_ngen_2145_ = lean_ctor_get(v___x_2141_, 2);
v_auxDeclNGen_2146_ = lean_ctor_get(v___x_2141_, 3);
v_cache_2147_ = lean_ctor_get(v___x_2141_, 5);
v_recordedDeps_2148_ = lean_ctor_get(v___x_2141_, 6);
v_messages_2149_ = lean_ctor_get(v___x_2141_, 7);
v_infoState_2150_ = lean_ctor_get(v___x_2141_, 8);
v_snapshotTasks_2151_ = lean_ctor_get(v___x_2141_, 9);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2153_ = v___x_2141_;
v_isShared_2154_ = v_isSharedCheck_2170_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_snapshotTasks_2151_);
lean_inc(v_infoState_2150_);
lean_inc(v_messages_2149_);
lean_inc(v_recordedDeps_2148_);
lean_inc(v_cache_2147_);
lean_inc(v_traceState_2142_);
lean_inc(v_auxDeclNGen_2146_);
lean_inc(v_ngen_2145_);
lean_inc(v_nextMacroScope_2144_);
lean_inc(v_env_2143_);
lean_dec(v___x_2141_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2170_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
uint64_t v_tid_2155_; lean_object* v_traces_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2169_; 
v_tid_2155_ = lean_ctor_get_uint64(v_traceState_2142_, sizeof(void*)*1);
v_traces_2156_ = lean_ctor_get(v_traceState_2142_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_traceState_2142_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2158_ = v_traceState_2142_;
v_isShared_2159_ = v_isSharedCheck_2169_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_traces_2156_);
lean_dec(v_traceState_2142_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2169_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2101_, v_traces_2156_);
lean_dec_ref(v_traces_2156_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2160_);
lean_ctor_set_uint64(v_reuseFailAlloc_2168_, sizeof(void*)*1, v_tid_2155_);
v___x_2162_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 4, v___x_2162_);
v___x_2164_ = v___x_2153_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_env_2143_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_nextMacroScope_2144_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_ngen_2145_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_auxDeclNGen_2146_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2167_, 5, v_cache_2147_);
lean_ctor_set(v_reuseFailAlloc_2167_, 6, v_recordedDeps_2148_);
lean_ctor_set(v_reuseFailAlloc_2167_, 7, v_messages_2149_);
lean_ctor_set(v_reuseFailAlloc_2167_, 8, v_infoState_2150_);
lean_ctor_set(v_reuseFailAlloc_2167_, 9, v_snapshotTasks_2151_);
v___x_2164_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_st_ref_put(v___y_2109_, v___x_2164_);
v___x_2166_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2111_);
return v___x_2166_;
}
}
}
}
}
else
{
goto v___jp_2134_;
}
}
else
{
goto v___jp_2134_;
}
}
v___jp_2171_:
{
double v___x_2173_; double v___x_2174_; double v___x_2175_; uint8_t v___x_2176_; 
v___x_2173_ = lean_unbox_float(v_snd_2120_);
v___x_2174_ = lean_unbox_float(v_fst_2119_);
v___x_2175_ = lean_float_sub(v___x_2173_, v___x_2174_);
v___x_2176_ = lean_float_decLt(v___y_2172_, v___x_2175_);
v___y_2140_ = v___x_2176_;
goto v___jp_2139_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2096_ = stack[0].m_obj;
uint8_t v_collapsed_2097_ = stack[1].m_num;
lean_object* v_tag_2098_ = stack[2].m_obj;
lean_object* v_opts_2099_ = stack[3].m_obj;
uint8_t v_clsEnabled_2100_ = stack[4].m_num;
lean_object* v_oldTraces_2101_ = stack[5].m_obj;
lean_object* v_msg_2102_ = stack[6].m_obj;
lean_object* v_resStartStop_2103_ = stack[7].m_obj;
lean_object* v___y_2104_ = stack[8].m_obj;
lean_object* v___y_2105_ = stack[9].m_obj;
lean_object* v___y_2106_ = stack[10].m_obj;
lean_object* v___y_2107_ = stack[11].m_obj;
lean_object* v___y_2108_ = stack[12].m_obj;
lean_object* v___y_2109_ = stack[13].m_obj;
lean_object* v_res_2187_;
v_res_2187_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_cls_2096_, v_collapsed_2097_, v_tag_2098_, v_opts_2099_, v_clsEnabled_2100_, v_oldTraces_2101_, v_msg_2102_, v_resStartStop_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
stack->m_obj
 = v_res_2187_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object* v_cls_2188_, lean_object* v_collapsed_2189_, lean_object* v_tag_2190_, lean_object* v_opts_2191_, lean_object* v_clsEnabled_2192_, lean_object* v_oldTraces_2193_, lean_object* v_msg_2194_, lean_object* v_resStartStop_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v_collapsed_boxed_2203_; uint8_t v_clsEnabled_boxed_2204_; lean_object* v_res_2205_; 
v_collapsed_boxed_2203_ = lean_unbox(v_collapsed_2189_);
v_clsEnabled_boxed_2204_ = lean_unbox(v_clsEnabled_2192_);
v_res_2205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_cls_2188_, v_collapsed_boxed_2203_, v_tag_2190_, v_opts_2191_, v_clsEnabled_boxed_2204_, v_oldTraces_2193_, v_msg_2194_, v_resStartStop_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec_ref(v_opts_2191_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v_ks_2210_; lean_object* v_vs_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2235_; 
v_ks_2210_ = lean_ctor_get(v_x_2206_, 0);
v_vs_2211_ = lean_ctor_get(v_x_2206_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_x_2206_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2213_ = v_x_2206_;
v_isShared_2214_ = v_isSharedCheck_2235_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_vs_2211_);
lean_inc(v_ks_2210_);
lean_dec(v_x_2206_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2235_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_array_get_size(v_ks_2210_);
v___x_2216_ = lean_nat_dec_lt(v_x_2207_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_dec(v_x_2207_);
v___x_2217_ = lean_array_push(v_ks_2210_, v_x_2208_);
v___x_2218_ = lean_array_push(v_vs_2211_, v_x_2209_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2218_);
lean_ctor_set(v___x_2213_, 0, v___x_2217_);
v___x_2220_ = v___x_2213_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
else
{
lean_object* v_k_x27_2222_; uint8_t v___x_2223_; 
v_k_x27_2222_ = lean_array_fget_borrowed(v_ks_2210_, v_x_2207_);
v___x_2223_ = l_Lean_instBEqMVarId_beq(v_x_2208_, v_k_x27_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2225_; 
if (v_isShared_2214_ == 0)
{
v___x_2225_ = v___x_2213_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_ks_2210_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_vs_2211_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_add(v_x_2207_, v___x_2226_);
lean_dec(v_x_2207_);
v_x_2206_ = v___x_2225_;
v_x_2207_ = v___x_2227_;
goto _start;
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_array_fset(v_ks_2210_, v_x_2207_, v_x_2208_);
v___x_2231_ = lean_array_fset(v_vs_2211_, v_x_2207_, v_x_2209_);
lean_dec(v_x_2207_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2231_);
lean_ctor_set(v___x_2213_, 0, v___x_2230_);
v___x_2233_ = v___x_2213_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_n_2236_, lean_object* v_k_2237_, lean_object* v_v_2238_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_n_2236_, v___x_2239_, v_k_2237_, v_v_2238_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2241_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2242_, size_t v_x_2243_, size_t v_x_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
if (lean_obj_tag(v_x_2242_) == 0)
{
lean_object* v_es_2247_; size_t v___x_2248_; size_t v___x_2249_; lean_object* v_j_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_es_2247_ = lean_ctor_get(v_x_2242_, 0);
v___x_2248_ = ((size_t)31ULL);
v___x_2249_ = lean_usize_land(v_x_2243_, v___x_2248_);
v_j_2250_ = lean_usize_to_nat(v___x_2249_);
v___x_2251_ = lean_array_get_size(v_es_2247_);
v___x_2252_ = lean_nat_dec_lt(v_j_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_dec(v_j_2250_);
lean_dec(v_x_2246_);
lean_dec(v_x_2245_);
return v_x_2242_;
}
else
{
lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2291_; 
lean_inc_ref(v_es_2247_);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_x_2242_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v_x_2242_, 0);
lean_dec(v_unused_2292_);
v___x_2254_ = v_x_2242_;
v_isShared_2255_ = v_isSharedCheck_2291_;
goto v_resetjp_2253_;
}
else
{
lean_dec(v_x_2242_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2291_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_v_2256_; lean_object* v___x_2257_; lean_object* v_xs_x27_2258_; lean_object* v___y_2260_; 
v_v_2256_ = lean_array_fget(v_es_2247_, v_j_2250_);
v___x_2257_ = lean_box(0);
v_xs_x27_2258_ = lean_array_fset(v_es_2247_, v_j_2250_, v___x_2257_);
switch(lean_obj_tag(v_v_2256_))
{
case 0:
{
lean_object* v_key_2265_; lean_object* v_val_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2276_; 
v_key_2265_ = lean_ctor_get(v_v_2256_, 0);
v_val_2266_ = lean_ctor_get(v_v_2256_, 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_v_2256_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2268_ = v_v_2256_;
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_val_2266_);
lean_inc(v_key_2265_);
lean_dec(v_v_2256_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_instBEqMVarId_beq(v_x_2245_, v_key_2265_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_del_object(v___x_2268_);
v___x_2271_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2265_, v_val_2266_, v_x_2245_, v_x_2246_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___y_2260_ = v___x_2272_;
goto v___jp_2259_;
}
else
{
lean_object* v___x_2274_; 
lean_dec(v_val_2266_);
lean_dec(v_key_2265_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_x_2246_);
lean_ctor_set(v___x_2268_, 0, v_x_2245_);
v___x_2274_ = v___x_2268_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_x_2245_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_x_2246_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
v___y_2260_ = v___x_2274_;
goto v___jp_2259_;
}
}
}
}
case 1:
{
lean_object* v_node_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2289_; 
v_node_2277_ = lean_ctor_get(v_v_2256_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_v_2256_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2279_ = v_v_2256_;
v_isShared_2280_ = v_isSharedCheck_2289_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_node_2277_);
lean_dec(v_v_2256_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2289_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
size_t v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2281_ = ((size_t)5ULL);
v___x_2282_ = lean_usize_shift_right(v_x_2243_, v___x_2281_);
v___x_2283_ = ((size_t)1ULL);
v___x_2284_ = lean_usize_add(v_x_2244_, v___x_2283_);
v___x_2285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_node_2277_, v___x_2282_, v___x_2284_, v_x_2245_, v_x_2246_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2285_);
v___x_2287_ = v___x_2279_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
v___y_2260_ = v___x_2287_;
goto v___jp_2259_;
}
}
}
default: 
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_x_2245_);
lean_ctor_set(v___x_2290_, 1, v_x_2246_);
v___y_2260_ = v___x_2290_;
goto v___jp_2259_;
}
}
v___jp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = lean_array_fset(v_xs_x27_2258_, v_j_2250_, v___y_2260_);
lean_dec(v_j_2250_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2261_);
v___x_2263_ = v___x_2254_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
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
else
{
lean_object* v_ks_2293_; lean_object* v_vs_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2312_; 
v_ks_2293_ = lean_ctor_get(v_x_2242_, 0);
v_vs_2294_ = lean_ctor_get(v_x_2242_, 1);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_x_2242_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2296_ = v_x_2242_;
v_isShared_2297_ = v_isSharedCheck_2312_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_vs_2294_);
lean_inc(v_ks_2293_);
lean_dec(v_x_2242_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2312_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_ks_2293_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_vs_2294_);
v___x_2299_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v_newNode_2300_; size_t v___x_2301_; uint8_t v___x_2302_; 
v_newNode_2300_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v___x_2299_, v_x_2245_, v_x_2246_);
v___x_2301_ = ((size_t)7ULL);
v___x_2302_ = lean_usize_dec_le(v___x_2301_, v_x_2244_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2303_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2300_);
v___x_2304_ = lean_unsigned_to_nat(4u);
v___x_2305_ = lean_nat_dec_lt(v___x_2303_, v___x_2304_);
lean_dec(v___x_2303_);
if (v___x_2305_ == 0)
{
lean_object* v_ks_2306_; lean_object* v_vs_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_ks_2306_ = lean_ctor_get(v_newNode_2300_, 0);
lean_inc_ref(v_ks_2306_);
v_vs_2307_ = lean_ctor_get(v_newNode_2300_, 1);
lean_inc_ref(v_vs_2307_);
lean_dec_ref(v_newNode_2300_);
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_2310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_x_2244_, v_ks_2306_, v_vs_2307_, v___x_2308_, v___x_2309_);
lean_dec_ref(v_vs_2307_);
lean_dec_ref(v_ks_2306_);
return v___x_2310_;
}
else
{
return v_newNode_2300_;
}
}
else
{
return v_newNode_2300_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2242_ = stack[0].m_obj;
size_t v_x_2243_ = stack[1].m_num;
size_t v_x_2244_ = stack[2].m_num;
lean_object* v_x_2245_ = stack[3].m_obj;
lean_object* v_x_2246_ = stack[4].m_obj;
lean_object* v_res_2313_;
v_res_2313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2242_, v_x_2243_, v_x_2244_, v_x_2245_, v_x_2246_);
stack->m_obj
 = v_res_2313_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t v_depth_2314_, lean_object* v_keys_2315_, lean_object* v_vals_2316_, lean_object* v_i_2317_, lean_object* v_entries_2318_){
_start:
{
lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2319_ = lean_array_get_size(v_keys_2315_);
v___x_2320_ = lean_nat_dec_lt(v_i_2317_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_dec(v_i_2317_);
return v_entries_2318_;
}
else
{
lean_object* v_k_2321_; lean_object* v_v_2322_; uint64_t v___x_2323_; size_t v_h_2324_; size_t v___x_2325_; lean_object* v___x_2326_; size_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; size_t v_h_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_k_2321_ = lean_array_fget_borrowed(v_keys_2315_, v_i_2317_);
v_v_2322_ = lean_array_fget_borrowed(v_vals_2316_, v_i_2317_);
v___x_2323_ = l_Lean_instHashableMVarId_hash(v_k_2321_);
v_h_2324_ = lean_uint64_to_usize(v___x_2323_);
v___x_2325_ = ((size_t)5ULL);
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = ((size_t)1ULL);
v___x_2328_ = lean_usize_sub(v_depth_2314_, v___x_2327_);
v___x_2329_ = lean_usize_mul(v___x_2325_, v___x_2328_);
v_h_2330_ = lean_usize_shift_right(v_h_2324_, v___x_2329_);
v___x_2331_ = lean_nat_add(v_i_2317_, v___x_2326_);
lean_dec(v_i_2317_);
lean_inc(v_v_2322_);
lean_inc(v_k_2321_);
v___x_2332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_entries_2318_, v_h_2330_, v_depth_2314_, v_k_2321_, v_v_2322_);
v_i_2317_ = v___x_2331_;
v_entries_2318_ = v___x_2332_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2314_ = stack[0].m_num;
lean_object* v_keys_2315_ = stack[1].m_obj;
lean_object* v_vals_2316_ = stack[2].m_obj;
lean_object* v_i_2317_ = stack[3].m_obj;
lean_object* v_entries_2318_ = stack[4].m_obj;
lean_object* v_res_2334_;
v_res_2334_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2314_, v_keys_2315_, v_vals_2316_, v_i_2317_, v_entries_2318_);
stack->m_obj
 = v_res_2334_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_depth_2335_, lean_object* v_keys_2336_, lean_object* v_vals_2337_, lean_object* v_i_2338_, lean_object* v_entries_2339_){
_start:
{
size_t v_depth_boxed_2340_; lean_object* v_res_2341_; 
v_depth_boxed_2340_ = lean_unbox_usize(v_depth_2335_);
lean_dec(v_depth_2335_);
v_res_2341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_boxed_2340_, v_keys_2336_, v_vals_2337_, v_i_2338_, v_entries_2339_);
lean_dec_ref(v_vals_2337_);
lean_dec_ref(v_keys_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
size_t v_x_17680__boxed_2347_; size_t v_x_17681__boxed_2348_; lean_object* v_res_2349_; 
v_x_17680__boxed_2347_ = lean_unbox_usize(v_x_2343_);
lean_dec(v_x_2343_);
v_x_17681__boxed_2348_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_res_2349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2342_, v_x_17680__boxed_2347_, v_x_17681__boxed_2348_, v_x_2345_, v_x_2346_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object* v_x_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_){
_start:
{
uint64_t v___x_2353_; size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2353_ = l_Lean_instHashableMVarId_hash(v_x_2351_);
v___x_2354_ = lean_uint64_to_usize(v___x_2353_);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2350_, v___x_2354_, v___x_2355_, v_x_2351_, v_x_2352_);
return v___x_2356_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v_mvarId_2357_, lean_object* v_val_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; lean_object* v_mctx_2362_; lean_object* v_cache_2363_; lean_object* v_zetaDeltaFVarIds_2364_; lean_object* v_postponed_2365_; lean_object* v_diag_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2396_; 
v___x_2361_ = lean_st_ref_take(v___y_2359_);
v_mctx_2362_ = lean_ctor_get(v___x_2361_, 0);
v_cache_2363_ = lean_ctor_get(v___x_2361_, 1);
v_zetaDeltaFVarIds_2364_ = lean_ctor_get(v___x_2361_, 2);
v_postponed_2365_ = lean_ctor_get(v___x_2361_, 3);
v_diag_2366_ = lean_ctor_get(v___x_2361_, 4);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2368_ = v___x_2361_;
v_isShared_2369_ = v_isSharedCheck_2396_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_diag_2366_);
lean_inc(v_postponed_2365_);
lean_inc(v_zetaDeltaFVarIds_2364_);
lean_inc(v_cache_2363_);
lean_inc(v_mctx_2362_);
lean_dec(v___x_2361_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2396_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v_depth_2370_; lean_object* v_levelAssignDepth_2371_; lean_object* v_lmvarCounter_2372_; lean_object* v_mvarCounter_2373_; lean_object* v_lDecls_2374_; lean_object* v_decls_2375_; lean_object* v_userNames_2376_; lean_object* v_lAssignment_2377_; lean_object* v_eAssignment_2378_; lean_object* v_dAssignment_2379_; lean_object* v_instanceTypedMVars_2380_; lean_object* v_synthNormMemo_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2395_; 
v_depth_2370_ = lean_ctor_get(v_mctx_2362_, 0);
v_levelAssignDepth_2371_ = lean_ctor_get(v_mctx_2362_, 1);
v_lmvarCounter_2372_ = lean_ctor_get(v_mctx_2362_, 2);
v_mvarCounter_2373_ = lean_ctor_get(v_mctx_2362_, 3);
v_lDecls_2374_ = lean_ctor_get(v_mctx_2362_, 4);
v_decls_2375_ = lean_ctor_get(v_mctx_2362_, 5);
v_userNames_2376_ = lean_ctor_get(v_mctx_2362_, 6);
v_lAssignment_2377_ = lean_ctor_get(v_mctx_2362_, 7);
v_eAssignment_2378_ = lean_ctor_get(v_mctx_2362_, 8);
v_dAssignment_2379_ = lean_ctor_get(v_mctx_2362_, 9);
v_instanceTypedMVars_2380_ = lean_ctor_get(v_mctx_2362_, 10);
v_synthNormMemo_2381_ = lean_ctor_get(v_mctx_2362_, 11);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_mctx_2362_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2383_ = v_mctx_2362_;
v_isShared_2384_ = v_isSharedCheck_2395_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_synthNormMemo_2381_);
lean_inc(v_instanceTypedMVars_2380_);
lean_inc(v_dAssignment_2379_);
lean_inc(v_eAssignment_2378_);
lean_inc(v_lAssignment_2377_);
lean_inc(v_userNames_2376_);
lean_inc(v_decls_2375_);
lean_inc(v_lDecls_2374_);
lean_inc(v_mvarCounter_2373_);
lean_inc(v_lmvarCounter_2372_);
lean_inc(v_levelAssignDepth_2371_);
lean_inc(v_depth_2370_);
lean_dec(v_mctx_2362_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2395_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2385_ = lean_box(0);
v___x_2386_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_eAssignment_2378_, v_mvarId_2357_, v_val_2358_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 8, v___x_2386_);
v___x_2388_ = v___x_2383_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_depth_2370_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_levelAssignDepth_2371_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_lmvarCounter_2372_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_mvarCounter_2373_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_lDecls_2374_);
lean_ctor_set(v_reuseFailAlloc_2394_, 5, v_decls_2375_);
lean_ctor_set(v_reuseFailAlloc_2394_, 6, v_userNames_2376_);
lean_ctor_set(v_reuseFailAlloc_2394_, 7, v_lAssignment_2377_);
lean_ctor_set(v_reuseFailAlloc_2394_, 8, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2394_, 9, v_dAssignment_2379_);
lean_ctor_set(v_reuseFailAlloc_2394_, 10, v_instanceTypedMVars_2380_);
lean_ctor_set(v_reuseFailAlloc_2394_, 11, v_synthNormMemo_2381_);
v___x_2388_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2388_);
v___x_2390_ = v___x_2368_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_cache_2363_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_zetaDeltaFVarIds_2364_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_postponed_2365_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v_diag_2366_);
v___x_2390_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_st_ref_put(v___y_2359_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2385_);
return v___x_2392_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2357_ = stack[0].m_obj;
lean_object* v_val_2358_ = stack[1].m_obj;
lean_object* v___y_2359_ = stack[2].m_obj;
lean_object* v_res_2397_;
v_res_2397_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2357_, v_val_2358_, v___y_2359_);
stack->m_obj
 = v_res_2397_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object* v_mvarId_2398_, lean_object* v_val_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2398_, v_val_2399_, v___y_2400_);
lean_dec(v___y_2400_);
return v_res_2402_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_keys_2403_, lean_object* v_i_2404_, lean_object* v_k_2405_){
_start:
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = lean_array_get_size(v_keys_2403_);
v___x_2407_ = lean_nat_dec_lt(v_i_2404_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec(v_i_2404_);
return v___x_2407_;
}
else
{
lean_object* v_k_x27_2408_; uint8_t v___x_2409_; 
v_k_x27_2408_ = lean_array_fget_borrowed(v_keys_2403_, v_i_2404_);
v___x_2409_ = l_Lean_instBEqMVarId_beq(v_k_2405_, v_k_x27_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_nat_add(v_i_2404_, v___x_2410_);
lean_dec(v_i_2404_);
v_i_2404_ = v___x_2411_;
goto _start;
}
else
{
lean_dec(v_i_2404_);
return v___x_2407_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2403_ = stack[0].m_obj;
lean_object* v_i_2404_ = stack[1].m_obj;
lean_object* v_k_2405_ = stack[2].m_obj;
uint8_t v_res_2413_;
v_res_2413_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2403_, v_i_2404_, v_k_2405_);
stack->m_num = v_res_2413_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_keys_2414_, lean_object* v_i_2415_, lean_object* v_k_2416_){
_start:
{
uint8_t v_res_2417_; lean_object* v_r_2418_; 
v_res_2417_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2414_, v_i_2415_, v_k_2416_);
lean_dec(v_k_2416_);
lean_dec_ref(v_keys_2414_);
v_r_2418_ = lean_box(v_res_2417_);
return v_r_2418_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(lean_object* v_x_2419_, size_t v_x_2420_, lean_object* v_x_2421_){
_start:
{
if (lean_obj_tag(v_x_2419_) == 0)
{
lean_object* v_es_2422_; lean_object* v___x_2423_; size_t v___x_2424_; size_t v___x_2425_; lean_object* v_j_2426_; lean_object* v___x_2427_; 
v_es_2422_ = lean_ctor_get(v_x_2419_, 0);
v___x_2423_ = lean_box(2);
v___x_2424_ = ((size_t)31ULL);
v___x_2425_ = lean_usize_land(v_x_2420_, v___x_2424_);
v_j_2426_ = lean_usize_to_nat(v___x_2425_);
v___x_2427_ = lean_array_get_borrowed(v___x_2423_, v_es_2422_, v_j_2426_);
lean_dec(v_j_2426_);
switch(lean_obj_tag(v___x_2427_))
{
case 0:
{
lean_object* v_key_2428_; uint8_t v___x_2429_; 
v_key_2428_ = lean_ctor_get(v___x_2427_, 0);
v___x_2429_ = l_Lean_instBEqMVarId_beq(v_x_2421_, v_key_2428_);
return v___x_2429_;
}
case 1:
{
lean_object* v_node_2430_; size_t v___x_2431_; size_t v___x_2432_; 
v_node_2430_ = lean_ctor_get(v___x_2427_, 0);
v___x_2431_ = ((size_t)5ULL);
v___x_2432_ = lean_usize_shift_right(v_x_2420_, v___x_2431_);
v_x_2419_ = v_node_2430_;
v_x_2420_ = v___x_2432_;
goto _start;
}
default: 
{
uint8_t v___x_2434_; 
v___x_2434_ = 0;
return v___x_2434_;
}
}
}
else
{
lean_object* v_ks_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v_ks_2435_ = lean_ctor_get(v_x_2419_, 0);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_ks_2435_, v___x_2436_, v_x_2421_);
return v___x_2437_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2419_ = stack[0].m_obj;
size_t v_x_2420_ = stack[1].m_num;
lean_object* v_x_2421_ = stack[2].m_obj;
uint8_t v_res_2438_;
v_res_2438_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2419_, v_x_2420_, v_x_2421_);
stack->m_num = v_res_2438_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
size_t v_x_18022__boxed_2442_; uint8_t v_res_2443_; lean_object* v_r_2444_; 
v_x_18022__boxed_2442_ = lean_unbox_usize(v_x_2440_);
lean_dec(v_x_2440_);
v_res_2443_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2439_, v_x_18022__boxed_2442_, v_x_2441_);
lean_dec(v_x_2441_);
lean_dec_ref(v_x_2439_);
v_r_2444_ = lean_box(v_res_2443_);
return v_r_2444_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(lean_object* v_x_2445_, lean_object* v_x_2446_){
_start:
{
uint64_t v___x_2447_; size_t v___x_2448_; uint8_t v___x_2449_; 
v___x_2447_ = l_Lean_instHashableMVarId_hash(v_x_2446_);
v___x_2448_ = lean_uint64_to_usize(v___x_2447_);
v___x_2449_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2445_, v___x_2448_, v_x_2446_);
return v___x_2449_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2445_ = stack[0].m_obj;
lean_object* v_x_2446_ = stack[1].m_obj;
uint8_t v_res_2450_;
v_res_2450_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2445_, v_x_2446_);
stack->m_num = v_res_2450_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg___boxed(lean_object* v_x_2451_, lean_object* v_x_2452_){
_start:
{
uint8_t v_res_2453_; lean_object* v_r_2454_; 
v_res_2453_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2451_, v_x_2452_);
lean_dec(v_x_2452_);
lean_dec_ref(v_x_2451_);
v_r_2454_ = lean_box(v_res_2453_);
return v_r_2454_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(lean_object* v_mvarId_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v_mctx_2459_; lean_object* v_eAssignment_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2458_ = lean_st_ref_get(v___y_2456_);
v_mctx_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_mctx_2459_);
lean_dec(v___x_2458_);
v_eAssignment_2460_ = lean_ctor_get(v_mctx_2459_, 8);
lean_inc_ref(v_eAssignment_2460_);
lean_dec_ref(v_mctx_2459_);
v___x_2461_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_eAssignment_2460_, v_mvarId_2455_);
lean_dec_ref(v_eAssignment_2460_);
v___x_2462_ = lean_box(v___x_2461_);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2455_ = stack[0].m_obj;
lean_object* v___y_2456_ = stack[1].m_obj;
lean_object* v_res_2464_;
v_res_2464_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2455_, v___y_2456_);
stack->m_obj
 = v_res_2464_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg___boxed(lean_object* v_mvarId_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec(v_mvarId_2465_);
return v_res_2468_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2469_; double v___x_2470_; 
v___x_2469_ = lean_unsigned_to_nat(1000000000u);
v___x_2470_ = lean_float_of_nat(v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1));
v___x_2473_ = l_Lean_stringToMessageData(v___x_2472_);
return v___x_2473_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(lean_object* v___x_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v___x_2474_, v___y_2478_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2654_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2654_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2654_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_unbox(v_a_2483_);
lean_dec(v_a_2483_);
if (v___x_2487_ == 0)
{
uint8_t v___x_2488_; lean_object* v___x_2489_; 
lean_del_object(v___x_2485_);
v___x_2488_ = 1;
lean_inc(v___x_2474_);
v___x_2489_ = l_Lean_MVarId_getType(v___x_2474_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_toCold_2490_; lean_object* v_options_2491_; uint8_t v_hasTrace_2492_; 
v_toCold_2490_ = lean_ctor_get(v___y_2479_, 0);
v_options_2491_ = lean_ctor_get(v_toCold_2490_, 2);
v_hasTrace_2492_ = lean_ctor_get_uint8(v_options_2491_, sizeof(void*)*1);
if (v_hasTrace_2492_ == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2494_ = l_Lean_Meta_mkDefault(v_a_2493_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2474_, v_a_2495_, v___y_2478_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2504_; 
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v___x_2496_, 0);
lean_dec(v_unused_2505_);
v___x_2498_ = v___x_2496_;
v_isShared_2499_ = v_isSharedCheck_2504_;
goto v_resetjp_2497_;
}
else
{
lean_dec(v___x_2496_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2504_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2500_ = lean_box(0);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2500_);
v___x_2502_ = v___x_2498_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
return v___x_2496_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v___x_2474_);
v_a_2506_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2494_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2494_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v_inheritedTraceOptions_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v_a_2524_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_a_2539_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v_a_2544_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v_a_2555_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v_a_2567_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v_a_2572_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; 
v_a_2514_ = lean_ctor_get(v___x_2489_, 0);
lean_inc_n(v_a_2514_, 2);
lean_dec_ref_known(v___x_2489_, 1);
v_inheritedTraceOptions_2515_ = lean_ctor_get(v_toCold_2490_, 11);
v___f_2516_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2516_, 0, v_a_2514_);
v___x_2517_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2518_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_2519_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2520_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2515_, v_options_2491_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = l_Lean_trace_profiler;
v___x_2616_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2491_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref(v___f_2516_);
v___x_2617_ = l_Lean_Meta_mkDefault(v_a_2514_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc_n(v_a_2618_, 2);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2619_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2474_, v_a_2618_, v___y_2478_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2632_; 
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v___x_2619_, 0);
lean_dec(v_unused_2633_);
v___x_2621_ = v___x_2619_;
v_isShared_2622_ = v_isSharedCheck_2632_;
goto v_resetjp_2620_;
}
else
{
lean_dec(v___x_2619_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2632_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
if (v___x_2520_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_dec(v_a_2618_);
v___x_2623_ = lean_box(0);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_del_object(v___x_2621_);
v___x_2627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2628_ = lean_unsigned_to_nat(30u);
v___x_2629_ = l_Lean_inlineExprTrailing(v_a_2618_, v___x_2628_);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2627_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2517_, v___x_2630_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2631_;
}
}
}
else
{
lean_dec(v_a_2618_);
return v___x_2619_;
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v___x_2474_);
v_a_2634_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2617_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2617_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
goto v___jp_2580_;
}
}
else
{
goto v___jp_2580_;
}
v___jp_2521_:
{
lean_object* v___x_2525_; double v___x_2526_; double v___x_2527_; double v___x_2528_; double v___x_2529_; double v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2525_ = lean_io_mono_nanos_now();
v___x_2526_ = lean_float_of_nat(v___y_2523_);
v___x_2527_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_2528_ = lean_float_div(v___x_2526_, v___x_2527_);
v___x_2529_ = lean_float_of_nat(v___x_2525_);
v___x_2530_ = lean_float_div(v___x_2529_, v___x_2527_);
v___x_2531_ = lean_box_float(v___x_2528_);
v___x_2532_ = lean_box_float(v___x_2530_);
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v_a_2524_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2517_, v___x_2488_, v___x_2518_, v_options_2491_, v___x_2520_, v___y_2522_, v___f_2516_, v___x_2534_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2535_;
}
v___jp_2536_:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2539_);
v___y_2522_ = v___y_2537_;
v___y_2523_ = v___y_2538_;
v_a_2524_ = v___x_2540_;
goto v___jp_2521_;
}
v___jp_2541_:
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_a_2544_);
v___y_2522_ = v___y_2542_;
v___y_2523_ = v___y_2543_;
v_a_2524_ = v___x_2545_;
goto v___jp_2521_;
}
v___jp_2546_:
{
if (lean_obj_tag(v___y_2549_) == 0)
{
lean_object* v_a_2550_; 
v_a_2550_ = lean_ctor_get(v___y_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___y_2549_, 1);
v___y_2542_ = v___y_2547_;
v___y_2543_ = v___y_2548_;
v_a_2544_ = v_a_2550_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2551_; 
v_a_2551_ = lean_ctor_get(v___y_2549_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___y_2549_, 1);
v___y_2537_ = v___y_2547_;
v___y_2538_ = v___y_2548_;
v_a_2539_ = v_a_2551_;
goto v___jp_2536_;
}
}
v___jp_2552_:
{
lean_object* v___x_2556_; double v___x_2557_; double v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2556_ = lean_io_get_num_heartbeats();
v___x_2557_ = lean_float_of_nat(v___y_2554_);
v___x_2558_ = lean_float_of_nat(v___x_2556_);
v___x_2559_ = lean_box_float(v___x_2557_);
v___x_2560_ = lean_box_float(v___x_2558_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v_a_2555_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2517_, v___x_2488_, v___x_2518_, v_options_2491_, v___x_2520_, v___y_2553_, v___f_2516_, v___x_2562_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2563_;
}
v___jp_2564_:
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_a_2567_);
v___y_2553_ = v___y_2565_;
v___y_2554_ = v___y_2566_;
v_a_2555_ = v___x_2568_;
goto v___jp_2552_;
}
v___jp_2569_:
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_a_2572_);
v___y_2553_ = v___y_2570_;
v___y_2554_ = v___y_2571_;
v_a_2555_ = v___x_2573_;
goto v___jp_2552_;
}
v___jp_2574_:
{
if (lean_obj_tag(v___y_2577_) == 0)
{
lean_object* v_a_2578_; 
v_a_2578_ = lean_ctor_get(v___y_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___y_2577_, 1);
v___y_2570_ = v___y_2575_;
v___y_2571_ = v___y_2576_;
v_a_2572_ = v_a_2578_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2579_; 
v_a_2579_ = lean_ctor_get(v___y_2577_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___y_2577_, 1);
v___y_2565_ = v___y_2575_;
v___y_2566_ = v___y_2576_;
v_a_2567_ = v_a_2579_;
goto v___jp_2564_;
}
}
v___jp_2580_:
{
lean_object* v___x_2581_; 
v___x_2581_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_2480_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2584_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2491_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_io_mono_nanos_now();
v___x_2586_ = l_Lean_Meta_mkDefault(v_a_2514_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc_n(v_a_2587_, 2);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2474_, v_a_2587_, v___y_2478_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_dec_ref_known(v___x_2588_, 1);
if (v___x_2520_ == 0)
{
lean_object* v___x_2589_; 
lean_dec(v_a_2587_);
v___x_2589_ = lean_box(0);
v___y_2542_ = v_a_2582_;
v___y_2543_ = v___x_2585_;
v_a_2544_ = v___x_2589_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2591_ = lean_unsigned_to_nat(30u);
v___x_2592_ = l_Lean_inlineExprTrailing(v_a_2587_, v___x_2591_);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2590_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2517_, v___x_2593_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
v___y_2547_ = v_a_2582_;
v___y_2548_ = v___x_2585_;
v___y_2549_ = v___x_2594_;
goto v___jp_2546_;
}
}
else
{
lean_dec(v_a_2587_);
v___y_2547_ = v_a_2582_;
v___y_2548_ = v___x_2585_;
v___y_2549_ = v___x_2588_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2595_; 
lean_dec(v___x_2474_);
v_a_2595_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2586_, 1);
v___y_2537_ = v_a_2582_;
v___y_2538_ = v___x_2585_;
v_a_2539_ = v_a_2595_;
goto v___jp_2536_;
}
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_io_get_num_heartbeats();
v___x_2597_ = l_Lean_Meta_mkDefault(v_a_2514_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc_n(v_a_2598_, 2);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2474_, v_a_2598_, v___y_2478_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_dec_ref_known(v___x_2599_, 1);
if (v___x_2520_ == 0)
{
lean_object* v___x_2600_; 
lean_dec(v_a_2598_);
v___x_2600_ = lean_box(0);
v___y_2570_ = v_a_2582_;
v___y_2571_ = v___x_2596_;
v_a_2572_ = v___x_2600_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2601_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2602_ = lean_unsigned_to_nat(30u);
v___x_2603_ = l_Lean_inlineExprTrailing(v_a_2598_, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2601_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2517_, v___x_2604_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
v___y_2575_ = v_a_2582_;
v___y_2576_ = v___x_2596_;
v___y_2577_ = v___x_2605_;
goto v___jp_2574_;
}
}
else
{
lean_dec(v_a_2598_);
v___y_2575_ = v_a_2582_;
v___y_2576_ = v___x_2596_;
v___y_2577_ = v___x_2599_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_a_2606_; 
lean_dec(v___x_2474_);
v_a_2606_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2597_, 1);
v___y_2565_ = v_a_2582_;
v___y_2566_ = v___x_2596_;
v_a_2567_ = v_a_2606_;
goto v___jp_2564_;
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v___f_2516_);
lean_dec(v_a_2514_);
lean_dec(v___x_2474_);
v_a_2607_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2581_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2581_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v___x_2474_);
v_a_2642_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2489_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2489_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
lean_dec(v___x_2474_);
v___x_2650_ = lean_box(0);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2650_);
v___x_2652_ = v___x_2485_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
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
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v___x_2474_);
v_a_2655_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2482_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2482_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2474_ = stack[0].m_obj;
lean_object* v___y_2475_ = stack[1].m_obj;
lean_object* v___y_2476_ = stack[2].m_obj;
lean_object* v___y_2477_ = stack[3].m_obj;
lean_object* v___y_2478_ = stack[4].m_obj;
lean_object* v___y_2479_ = stack[5].m_obj;
lean_object* v___y_2480_ = stack[6].m_obj;
lean_object* v_res_2663_;
v_res_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
stack->m_obj
 = v_res_2663_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2672_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2673_, size_t v_i_2674_, size_t v_stop_2675_, lean_object* v_b_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v___x_2684_; 
v___x_2684_ = lean_usize_dec_eq(v_i_2674_, v_stop_2675_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; lean_object* v___f_2686_; lean_object* v___x_2687_; 
v___x_2685_ = lean_array_uget_borrowed(v_as_2673_, v_i_2674_);
lean_inc_n(v___x_2685_, 2);
v___f_2686_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2686_, 0, v___x_2685_);
v___x_2687_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2685_, v___f_2686_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; size_t v___x_2689_; size_t v___x_2690_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2689_ = ((size_t)1ULL);
v___x_2690_ = lean_usize_add(v_i_2674_, v___x_2689_);
v_i_2674_ = v___x_2690_;
v_b_2676_ = v_a_2688_;
goto _start;
}
else
{
return v___x_2687_;
}
}
else
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_b_2676_);
return v___x_2692_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2673_ = stack[0].m_obj;
size_t v_i_2674_ = stack[1].m_num;
size_t v_stop_2675_ = stack[2].m_num;
lean_object* v_b_2676_ = stack[3].m_obj;
lean_object* v___y_2677_ = stack[4].m_obj;
lean_object* v___y_2678_ = stack[5].m_obj;
lean_object* v___y_2679_ = stack[6].m_obj;
lean_object* v___y_2680_ = stack[7].m_obj;
lean_object* v___y_2681_ = stack[8].m_obj;
lean_object* v___y_2682_ = stack[9].m_obj;
lean_object* v_res_2693_;
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2673_, v_i_2674_, v_stop_2675_, v_b_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
stack->m_obj
 = v_res_2693_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2694_, lean_object* v_i_2695_, lean_object* v_stop_2696_, lean_object* v_b_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
size_t v_i_boxed_2705_; size_t v_stop_boxed_2706_; lean_object* v_res_2707_; 
v_i_boxed_2705_ = lean_unbox_usize(v_i_2695_);
lean_dec(v_i_2695_);
v_stop_boxed_2706_ = lean_unbox_usize(v_stop_2696_);
lean_dec(v_stop_2696_);
v_res_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2694_, v_i_boxed_2705_, v_stop_boxed_2706_, v_b_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_as_2694_);
return v_res_2707_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2708_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2738_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2738_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2738_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2721_ = lean_unsigned_to_nat(0u);
v___x_2722_ = lean_array_get_size(v_a_2717_);
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_nat_dec_lt(v___x_2721_, v___x_2722_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2726_; 
lean_dec(v_a_2717_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2723_);
v___x_2726_ = v___x_2719_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2723_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
else
{
uint8_t v___x_2728_; 
v___x_2728_ = lean_nat_dec_le(v___x_2722_, v___x_2722_);
if (v___x_2728_ == 0)
{
if (v___x_2724_ == 0)
{
lean_object* v___x_2730_; 
lean_dec(v_a_2717_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2723_);
v___x_2730_ = v___x_2719_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2723_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
else
{
size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
lean_del_object(v___x_2719_);
v___x_2732_ = ((size_t)0ULL);
v___x_2733_ = lean_usize_of_nat(v___x_2722_);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2717_, v___x_2732_, v___x_2733_, v___x_2723_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2717_);
return v___x_2734_;
}
}
else
{
size_t v___x_2735_; size_t v___x_2736_; lean_object* v___x_2737_; 
lean_del_object(v___x_2719_);
v___x_2735_ = ((size_t)0ULL);
v___x_2736_ = lean_usize_of_nat(v___x_2722_);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2717_, v___x_2735_, v___x_2736_, v___x_2723_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2717_);
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_a_2739_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2716_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2716_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2708_ = stack[0].m_obj;
lean_object* v_a_2709_ = stack[1].m_obj;
lean_object* v_a_2710_ = stack[2].m_obj;
lean_object* v_a_2711_ = stack[3].m_obj;
lean_object* v_a_2712_ = stack[4].m_obj;
lean_object* v_a_2713_ = stack[5].m_obj;
lean_object* v_a_2714_ = stack[6].m_obj;
lean_object* v_res_2747_;
v_res_2747_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
stack->m_obj
 = v_res_2747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
return v_res_2756_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2757_, v___y_2761_);
return v___x_2765_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2757_ = stack[0].m_obj;
lean_object* v___y_2758_ = stack[1].m_obj;
lean_object* v___y_2759_ = stack[2].m_obj;
lean_object* v___y_2760_ = stack[3].m_obj;
lean_object* v___y_2761_ = stack[4].m_obj;
lean_object* v___y_2762_ = stack[5].m_obj;
lean_object* v___y_2763_ = stack[6].m_obj;
lean_object* v_res_2766_;
v_res_2766_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
stack->m_obj
 = v_res_2766_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v_mvarId_2767_);
return v_res_2775_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v_mvarId_2776_, lean_object* v_val_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2776_, v_val_2777_, v___y_2781_);
return v___x_2785_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2776_ = stack[0].m_obj;
lean_object* v_val_2777_ = stack[1].m_obj;
lean_object* v___y_2778_ = stack[2].m_obj;
lean_object* v___y_2779_ = stack[3].m_obj;
lean_object* v___y_2780_ = stack[4].m_obj;
lean_object* v___y_2781_ = stack[5].m_obj;
lean_object* v___y_2782_ = stack[6].m_obj;
lean_object* v___y_2783_ = stack[7].m_obj;
lean_object* v_res_2786_;
v_res_2786_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2776_, v_val_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
stack->m_obj
 = v_res_2786_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v_mvarId_2787_, lean_object* v_val_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2787_, v_val_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2796_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object* v_00_u03b1_2797_, lean_object* v_x_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_2798_);
return v___x_2806_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2798_ = stack[1].m_obj;
lean_object* v___y_2799_ = stack[2].m_obj;
lean_object* v___y_2800_ = stack[3].m_obj;
lean_object* v___y_2801_ = stack[4].m_obj;
lean_object* v___y_2802_ = stack[5].m_obj;
lean_object* v___y_2803_ = stack[6].m_obj;
lean_object* v___y_2804_ = stack[7].m_obj;
lean_object* v_res_2807_;
v_res_2807_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_box(0), v_x_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
stack->m_obj
 = v_res_2807_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2808_, lean_object* v_x_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(v_00_u03b1_2808_, v_x_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2817_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2818_, lean_object* v_x_2819_, lean_object* v_x_2820_){
_start:
{
uint8_t v___x_2821_; 
v___x_2821_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2819_, v_x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2819_ = stack[1].m_obj;
lean_object* v_x_2820_ = stack[2].m_obj;
uint8_t v_res_2822_;
v_res_2822_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_box(0), v_x_2819_, v_x_2820_);
stack->m_num = v_res_2822_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_){
_start:
{
uint8_t v_res_2826_; lean_object* v_r_2827_; 
v_res_2826_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2823_, v_x_2824_, v_x_2825_);
lean_dec(v_x_2825_);
lean_dec_ref(v_x_2824_);
v_r_2827_ = lean_box(v_res_2826_);
return v_r_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object* v_00_u03b2_2828_, lean_object* v_x_2829_, lean_object* v_x_2830_, lean_object* v_x_2831_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_x_2829_, v_x_2830_, v_x_2831_);
return v___x_2832_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object* v_oldTraces_2833_, lean_object* v_data_2834_, lean_object* v_ref_2835_, lean_object* v_msg_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2833_, v_data_2834_, v_ref_2835_, v_msg_2836_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_2833_ = stack[0].m_obj;
lean_object* v_data_2834_ = stack[1].m_obj;
lean_object* v_ref_2835_ = stack[2].m_obj;
lean_object* v_msg_2836_ = stack[3].m_obj;
lean_object* v___y_2837_ = stack[4].m_obj;
lean_object* v___y_2838_ = stack[5].m_obj;
lean_object* v___y_2839_ = stack[6].m_obj;
lean_object* v___y_2840_ = stack[7].m_obj;
lean_object* v___y_2841_ = stack[8].m_obj;
lean_object* v___y_2842_ = stack[9].m_obj;
lean_object* v_res_2845_;
v_res_2845_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_oldTraces_2833_, v_data_2834_, v_ref_2835_, v_msg_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
stack->m_obj
 = v_res_2845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object* v_oldTraces_2846_, lean_object* v_data_2847_, lean_object* v_ref_2848_, lean_object* v_msg_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_oldTraces_2846_, v_data_2847_, v_ref_2848_, v_msg_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
return v_res_2857_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2858_, lean_object* v_x_2859_, size_t v_x_2860_, lean_object* v_x_2861_){
_start:
{
uint8_t v___x_2862_; 
v___x_2862_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2859_, v_x_2860_, v_x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2859_ = stack[1].m_obj;
size_t v_x_2860_ = stack[2].m_num;
lean_object* v_x_2861_ = stack[3].m_obj;
uint8_t v_res_2863_;
v_res_2863_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_box(0), v_x_2859_, v_x_2860_, v_x_2861_);
stack->m_num = v_res_2863_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_, lean_object* v_x_2867_){
_start:
{
size_t v_x_19084__boxed_2868_; uint8_t v_res_2869_; lean_object* v_r_2870_; 
v_x_19084__boxed_2868_ = lean_unbox_usize(v_x_2866_);
lean_dec(v_x_2866_);
v_res_2869_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2864_, v_x_2865_, v_x_19084__boxed_2868_, v_x_2867_);
lean_dec(v_x_2867_);
lean_dec_ref(v_x_2865_);
v_r_2870_ = lean_box(v_res_2869_);
return v_r_2870_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2871_, lean_object* v_x_2872_, size_t v_x_2873_, size_t v_x_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2872_, v_x_2873_, v_x_2874_, v_x_2875_, v_x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2872_ = stack[1].m_obj;
size_t v_x_2873_ = stack[2].m_num;
size_t v_x_2874_ = stack[3].m_num;
lean_object* v_x_2875_ = stack[4].m_obj;
lean_object* v_x_2876_ = stack[5].m_obj;
lean_object* v_res_2878_;
v_res_2878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_box(0), v_x_2872_, v_x_2873_, v_x_2874_, v_x_2875_, v_x_2876_);
stack->m_obj
 = v_res_2878_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
size_t v_x_19102__boxed_2885_; size_t v_x_19103__boxed_2886_; lean_object* v_res_2887_; 
v_x_19102__boxed_2885_ = lean_unbox_usize(v_x_2881_);
lean_dec(v_x_2881_);
v_x_19103__boxed_2886_ = lean_unbox_usize(v_x_2882_);
lean_dec(v_x_2882_);
v_res_2887_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(v_00_u03b2_2879_, v_x_2880_, v_x_19102__boxed_2885_, v_x_19103__boxed_2886_, v_x_2883_, v_x_2884_);
return v_res_2887_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2888_, lean_object* v_keys_2889_, lean_object* v_vals_2890_, lean_object* v_heq_2891_, lean_object* v_i_2892_, lean_object* v_k_2893_){
_start:
{
uint8_t v___x_2894_; 
v___x_2894_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2889_, v_i_2892_, v_k_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2889_ = stack[1].m_obj;
lean_object* v_vals_2890_ = stack[2].m_obj;
lean_object* v_i_2892_ = stack[4].m_obj;
lean_object* v_k_2893_ = stack[5].m_obj;
uint8_t v_res_2895_;
v_res_2895_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_box(0), v_keys_2889_, v_vals_2890_, lean_box(0), v_i_2892_, v_k_2893_);
stack->m_num = v_res_2895_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2896_, lean_object* v_keys_2897_, lean_object* v_vals_2898_, lean_object* v_heq_2899_, lean_object* v_i_2900_, lean_object* v_k_2901_){
_start:
{
uint8_t v_res_2902_; lean_object* v_r_2903_; 
v_res_2902_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2896_, v_keys_2897_, v_vals_2898_, v_heq_2899_, v_i_2900_, v_k_2901_);
lean_dec(v_k_2901_);
lean_dec_ref(v_vals_2898_);
lean_dec_ref(v_keys_2897_);
v_r_2903_ = lean_box(v_res_2902_);
return v_r_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_2904_, lean_object* v_n_2905_, lean_object* v_k_2906_, lean_object* v_v_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v_n_2905_, v_k_2906_, v_v_2907_);
return v___x_2908_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b2_2909_, size_t v_depth_2910_, lean_object* v_keys_2911_, lean_object* v_vals_2912_, lean_object* v_heq_2913_, lean_object* v_i_2914_, lean_object* v_entries_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2910_, v_keys_2911_, v_vals_2912_, v_i_2914_, v_entries_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2910_ = stack[1].m_num;
lean_object* v_keys_2911_ = stack[2].m_obj;
lean_object* v_vals_2912_ = stack[3].m_obj;
lean_object* v_i_2914_ = stack[5].m_obj;
lean_object* v_entries_2915_ = stack[6].m_obj;
lean_object* v_res_2917_;
v_res_2917_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_box(0), v_depth_2910_, v_keys_2911_, v_vals_2912_, lean_box(0), v_i_2914_, v_entries_2915_);
stack->m_obj
 = v_res_2917_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b2_2918_, lean_object* v_depth_2919_, lean_object* v_keys_2920_, lean_object* v_vals_2921_, lean_object* v_heq_2922_, lean_object* v_i_2923_, lean_object* v_entries_2924_){
_start:
{
size_t v_depth_boxed_2925_; lean_object* v_res_2926_; 
v_depth_boxed_2925_ = lean_unbox_usize(v_depth_2919_);
lean_dec(v_depth_2919_);
v_res_2926_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(v_00_u03b2_2918_, v_depth_boxed_2925_, v_keys_2920_, v_vals_2921_, v_heq_2922_, v_i_2923_, v_entries_2924_);
lean_dec_ref(v_vals_2921_);
lean_dec_ref(v_keys_2920_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_x_2928_, v_x_2929_, v_x_2930_, v_x_2931_);
return v___x_2932_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v___x_2936_; 
v___x_2936_ = l_Lean_Expr_hasMVar(v_e_2933_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_e_2933_);
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; lean_object* v_mctx_2939_; lean_object* v___x_2940_; lean_object* v_fst_2941_; lean_object* v_snd_2942_; lean_object* v___x_2943_; lean_object* v_cache_2944_; lean_object* v_zetaDeltaFVarIds_2945_; lean_object* v_postponed_2946_; lean_object* v_diag_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2956_; 
v___x_2938_ = lean_st_ref_get(v___y_2934_);
v_mctx_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc_ref(v_mctx_2939_);
lean_dec(v___x_2938_);
v___x_2940_ = l_Lean_instantiateMVarsCore(v_mctx_2939_, v_e_2933_);
v_fst_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_fst_2941_);
v_snd_2942_ = lean_ctor_get(v___x_2940_, 1);
lean_inc(v_snd_2942_);
lean_dec_ref(v___x_2940_);
v___x_2943_ = lean_st_ref_take(v___y_2934_);
v_cache_2944_ = lean_ctor_get(v___x_2943_, 1);
v_zetaDeltaFVarIds_2945_ = lean_ctor_get(v___x_2943_, 2);
v_postponed_2946_ = lean_ctor_get(v___x_2943_, 3);
v_diag_2947_ = lean_ctor_get(v___x_2943_, 4);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v___x_2943_, 0);
lean_dec(v_unused_2957_);
v___x_2949_ = v___x_2943_;
v_isShared_2950_ = v_isSharedCheck_2956_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_diag_2947_);
lean_inc(v_postponed_2946_);
lean_inc(v_zetaDeltaFVarIds_2945_);
lean_inc(v_cache_2944_);
lean_dec(v___x_2943_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2956_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v_snd_2942_);
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_snd_2942_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_cache_2944_);
lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_zetaDeltaFVarIds_2945_);
lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_postponed_2946_);
lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_diag_2947_);
v___x_2952_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_st_ref_put(v___y_2934_, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_fst_2941_);
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2933_ = stack[0].m_obj;
lean_object* v___y_2934_ = stack[1].m_obj;
lean_object* v_res_2958_;
v_res_2958_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2933_, v___y_2934_);
stack->m_obj
 = v_res_2958_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2959_, v___y_2960_);
lean_dec(v___y_2960_);
return v_res_2962_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2963_, v___y_2967_);
return v___x_2971_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2963_ = stack[0].m_obj;
lean_object* v___y_2964_ = stack[1].m_obj;
lean_object* v___y_2965_ = stack[2].m_obj;
lean_object* v___y_2966_ = stack[3].m_obj;
lean_object* v___y_2967_ = stack[4].m_obj;
lean_object* v___y_2968_ = stack[5].m_obj;
lean_object* v___y_2969_ = stack[6].m_obj;
lean_object* v_res_2972_;
v_res_2972_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
stack->m_obj
 = v_res_2972_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
return v_res_2981_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_2982_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_21156__overap_2992_; lean_object* v___x_2993_; 
v___x_2991_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_21156__overap_2992_ = lean_panic_fn_borrowed(v___x_2991_, v_msg_2983_);
lean_inc(v___y_2989_);
lean_inc_ref(v___y_2988_);
lean_inc(v___y_2987_);
lean_inc_ref(v___y_2986_);
lean_inc(v___y_2985_);
lean_inc_ref(v___y_2984_);
v___x_2993_ = lean_apply_7(v___x_21156__overap_2992_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, lean_box(0));
return v___x_2993_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2983_ = stack[0].m_obj;
lean_object* v___y_2984_ = stack[1].m_obj;
lean_object* v___y_2985_ = stack[2].m_obj;
lean_object* v___y_2986_ = stack[3].m_obj;
lean_object* v___y_2987_ = stack[4].m_obj;
lean_object* v___y_2988_ = stack[5].m_obj;
lean_object* v___y_2989_ = stack[6].m_obj;
lean_object* v_res_2994_;
v_res_2994_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
stack->m_obj
 = v_res_2994_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
return v_res_3003_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object* v_a_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3004_ = stack[0].m_obj;
lean_object* v___y_3005_ = stack[1].m_obj;
lean_object* v___y_3006_ = stack[2].m_obj;
lean_object* v___y_3007_ = stack[3].m_obj;
lean_object* v___y_3008_ = stack[4].m_obj;
lean_object* v___y_3009_ = stack[5].m_obj;
lean_object* v___y_3010_ = stack[6].m_obj;
lean_object* v_res_3013_;
v_res_3013_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
stack->m_obj
 = v_res_3013_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object* v_a_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3022_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_00_u03b1_3023_, lean_object* v_a_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3024_ = stack[1].m_obj;
lean_object* v___y_3025_ = stack[2].m_obj;
lean_object* v___y_3026_ = stack[3].m_obj;
lean_object* v___y_3027_ = stack[4].m_obj;
lean_object* v___y_3028_ = stack[5].m_obj;
lean_object* v___y_3029_ = stack[6].m_obj;
lean_object* v___y_3030_ = stack[7].m_obj;
lean_object* v_res_3033_;
v_res_3033_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_box(0), v_a_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
stack->m_obj
 = v_res_3033_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_00_u03b1_3034_, lean_object* v_a_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_00_u03b1_3034_, v_a_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
return v_res_3043_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object* v_k_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v_b_3047_, lean_object* v_c_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; 
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___y_3050_);
lean_inc_ref(v___y_3049_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3045_);
v___x_3054_ = lean_apply_9(v_k_3044_, v_b_3047_, v_c_3048_, v___y_3045_, v___y_3046_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, lean_box(0));
return v___x_3054_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3044_ = stack[0].m_obj;
lean_object* v___y_3045_ = stack[1].m_obj;
lean_object* v___y_3046_ = stack[2].m_obj;
lean_object* v_b_3047_ = stack[3].m_obj;
lean_object* v_c_3048_ = stack[4].m_obj;
lean_object* v___y_3049_ = stack[5].m_obj;
lean_object* v___y_3050_ = stack[6].m_obj;
lean_object* v___y_3051_ = stack[7].m_obj;
lean_object* v___y_3052_ = stack[8].m_obj;
lean_object* v_res_3055_;
v_res_3055_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_3044_, v___y_3045_, v___y_3046_, v_b_3047_, v_c_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
stack->m_obj
 = v_res_3055_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object* v_k_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v_b_3059_, lean_object* v_c_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_3056_, v___y_3057_, v___y_3058_, v_b_3059_, v_c_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
return v_res_3066_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_type_3067_, lean_object* v_k_3068_, uint8_t v_cleanupAnnotations_3069_, uint8_t v_whnfType_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___f_3078_; lean_object* v___x_3079_; 
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3071_);
v___f_3078_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3078_, 0, v_k_3068_);
lean_closure_set(v___f_3078_, 1, v___y_3071_);
lean_closure_set(v___f_3078_, 2, v___y_3072_);
v___x_3079_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3067_, v___f_3078_, v_cleanupAnnotations_3069_, v_whnfType_3070_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3079_) == 0)
{
return v___x_3079_;
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3079_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3067_ = stack[0].m_obj;
lean_object* v_k_3068_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_3069_ = stack[2].m_num;
uint8_t v_whnfType_3070_ = stack[3].m_num;
lean_object* v___y_3071_ = stack[4].m_obj;
lean_object* v___y_3072_ = stack[5].m_obj;
lean_object* v___y_3073_ = stack[6].m_obj;
lean_object* v___y_3074_ = stack[7].m_obj;
lean_object* v___y_3075_ = stack[8].m_obj;
lean_object* v___y_3076_ = stack[9].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3067_, v_k_3068_, v_cleanupAnnotations_3069_, v_whnfType_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_type_3089_, lean_object* v_k_3090_, lean_object* v_cleanupAnnotations_3091_, lean_object* v_whnfType_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3100_; uint8_t v_whnfType_boxed_3101_; lean_object* v_res_3102_; 
v_cleanupAnnotations_boxed_3100_ = lean_unbox(v_cleanupAnnotations_3091_);
v_whnfType_boxed_3101_ = lean_unbox(v_whnfType_3092_);
v_res_3102_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3089_, v_k_3090_, v_cleanupAnnotations_boxed_3100_, v_whnfType_boxed_3101_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3102_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_3103_, lean_object* v_type_3104_, lean_object* v_k_3105_, uint8_t v_cleanupAnnotations_3106_, uint8_t v_whnfType_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3104_, v_k_3105_, v_cleanupAnnotations_3106_, v_whnfType_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3104_ = stack[1].m_obj;
lean_object* v_k_3105_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_3106_ = stack[3].m_num;
uint8_t v_whnfType_3107_ = stack[4].m_num;
lean_object* v___y_3108_ = stack[5].m_obj;
lean_object* v___y_3109_ = stack[6].m_obj;
lean_object* v___y_3110_ = stack[7].m_obj;
lean_object* v___y_3111_ = stack[8].m_obj;
lean_object* v___y_3112_ = stack[9].m_obj;
lean_object* v___y_3113_ = stack[10].m_obj;
lean_object* v_res_3116_;
v_res_3116_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_box(0), v_type_3104_, v_k_3105_, v_cleanupAnnotations_3106_, v_whnfType_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
stack->m_obj
 = v_res_3116_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_3117_, lean_object* v_type_3118_, lean_object* v_k_3119_, lean_object* v_cleanupAnnotations_3120_, lean_object* v_whnfType_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3129_; uint8_t v_whnfType_boxed_3130_; lean_object* v_res_3131_; 
v_cleanupAnnotations_boxed_3129_ = lean_unbox(v_cleanupAnnotations_3120_);
v_whnfType_boxed_3130_ = lean_unbox(v_whnfType_3121_);
v_res_3131_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_3117_, v_type_3118_, v_k_3119_, v_cleanupAnnotations_boxed_3129_, v_whnfType_boxed_3130_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
return v_res_3131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3134_ = l_Lean_stringToMessageData(v___x_3133_);
return v___x_3134_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3135_ = stack[0].m_obj;
lean_object* v___y_3136_ = stack[1].m_obj;
lean_object* v___y_3137_ = stack[2].m_obj;
lean_object* v___y_3138_ = stack[3].m_obj;
lean_object* v___y_3139_ = stack[4].m_obj;
lean_object* v___y_3140_ = stack[5].m_obj;
lean_object* v___y_3141_ = stack[6].m_obj;
lean_object* v_res_3145_;
v_res_3145_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
stack->m_obj
 = v_res_3145_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec_ref(v_x_3146_);
return v_res_3154_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v___x_3155_, lean_object* v_fst_3156_, lean_object* v_____r_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = l_Lean_mkAppN(v___x_3155_, v_fst_3156_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3155_ = stack[0].m_obj;
lean_object* v_fst_3156_ = stack[1].m_obj;
lean_object* v_____r_3157_ = stack[2].m_obj;
lean_object* v___y_3158_ = stack[3].m_obj;
lean_object* v___y_3159_ = stack[4].m_obj;
lean_object* v___y_3160_ = stack[5].m_obj;
lean_object* v___y_3161_ = stack[6].m_obj;
lean_object* v___y_3162_ = stack[7].m_obj;
lean_object* v___y_3163_ = stack[8].m_obj;
lean_object* v_res_3167_;
v_res_3167_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3155_, v_fst_3156_, v_____r_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
stack->m_obj
 = v_res_3167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v___x_3168_, lean_object* v_fst_3169_, lean_object* v_____r_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3168_, v_fst_3169_, v_____r_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v_fst_3169_);
return v_res_3178_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0));
v___x_3181_ = l_Lean_stringToMessageData(v___x_3180_);
return v___x_3181_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v_ctorName_3182_, uint8_t v___x_3183_, lean_object* v_x_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3192_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1);
v___x_3193_ = l_Lean_MessageData_ofConstName(v_ctorName_3182_, v___x_3183_);
v___x_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorName_3182_ = stack[0].m_obj;
uint8_t v___x_3183_ = stack[1].m_num;
lean_object* v_x_3184_ = stack[2].m_obj;
lean_object* v___y_3185_ = stack[3].m_obj;
lean_object* v___y_3186_ = stack[4].m_obj;
lean_object* v___y_3187_ = stack[5].m_obj;
lean_object* v___y_3188_ = stack[6].m_obj;
lean_object* v___y_3189_ = stack[7].m_obj;
lean_object* v___y_3190_ = stack[8].m_obj;
lean_object* v_res_3198_;
v_res_3198_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3182_, v___x_3183_, v_x_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
stack->m_obj
 = v_res_3198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v_ctorName_3199_, lean_object* v___x_3200_, lean_object* v_x_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v___x_26241__boxed_3209_; lean_object* v_res_3210_; 
v___x_26241__boxed_3209_ = lean_unbox(v___x_3200_);
v_res_3210_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3199_, v___x_26241__boxed_3209_, v_x_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec_ref(v_x_3201_);
return v_res_3210_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object* v_e_3211_){
_start:
{
if (lean_obj_tag(v_e_3211_) == 0)
{
uint8_t v___x_3212_; 
v___x_3212_ = 2;
return v___x_3212_;
}
else
{
lean_object* v_a_3213_; uint8_t v___x_3214_; 
v_a_3213_ = lean_ctor_get(v_e_3211_, 0);
v___x_3214_ = l_Lean_Expr_hasSyntheticSorry(v_a_3213_);
if (v___x_3214_ == 0)
{
uint8_t v___x_3215_; 
v___x_3215_ = 0;
return v___x_3215_;
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = 1;
return v___x_3216_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3211_ = stack[0].m_obj;
uint8_t v_res_3217_;
v_res_3217_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3211_);
stack->m_num = v_res_3217_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object* v_e_3218_){
_start:
{
uint8_t v_res_3219_; lean_object* v_r_3220_; 
v_res_3219_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3218_);
lean_dec_ref(v_e_3218_);
v_r_3220_ = lean_box(v_res_3219_);
return v_r_3220_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v_cls_3221_, uint8_t v_collapsed_3222_, lean_object* v_tag_3223_, lean_object* v_opts_3224_, uint8_t v_clsEnabled_3225_, lean_object* v_oldTraces_3226_, lean_object* v_msg_3227_, lean_object* v_resStartStop_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_fst_3236_; lean_object* v_snd_3237_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_data_3241_; lean_object* v_fst_3252_; lean_object* v_snd_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; lean_object* v___y_3257_; lean_object* v_a_3258_; uint8_t v___y_3273_; double v___y_3305_; 
v_fst_3236_ = lean_ctor_get(v_resStartStop_3228_, 0);
lean_inc(v_fst_3236_);
v_snd_3237_ = lean_ctor_get(v_resStartStop_3228_, 1);
lean_inc(v_snd_3237_);
lean_dec_ref(v_resStartStop_3228_);
v_fst_3252_ = lean_ctor_get(v_snd_3237_, 0);
lean_inc(v_fst_3252_);
v_snd_3253_ = lean_ctor_get(v_snd_3237_, 1);
lean_inc(v_snd_3253_);
lean_dec(v_snd_3237_);
v___x_3254_ = l_Lean_trace_profiler;
v___x_3255_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3224_, v___x_3254_);
if (v___x_3255_ == 0)
{
v___y_3273_ = v___x_3255_;
goto v___jp_3272_;
}
else
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3311_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3224_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; double v___x_3314_; double v___x_3315_; double v___x_3316_; 
v___x_3312_ = l_Lean_trace_profiler_threshold;
v___x_3313_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3224_, v___x_3312_);
v___x_3314_ = lean_float_of_nat(v___x_3313_);
v___x_3315_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_3316_ = lean_float_div(v___x_3314_, v___x_3315_);
v___y_3305_ = v___x_3316_;
goto v___jp_3304_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; double v___x_3319_; 
v___x_3317_ = l_Lean_trace_profiler_threshold;
v___x_3318_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3224_, v___x_3317_);
v___x_3319_ = lean_float_of_nat(v___x_3318_);
v___y_3305_ = v___x_3319_;
goto v___jp_3304_;
}
}
v___jp_3238_:
{
lean_object* v___x_3242_; 
lean_inc(v___y_3240_);
v___x_3242_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_3226_, v_data_3241_, v___y_3240_, v___y_3239_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; 
lean_dec_ref_known(v___x_3242_, 1);
v___x_3243_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3236_);
return v___x_3243_;
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_fst_3236_);
v_a_3244_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3242_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
v___jp_3256_:
{
uint8_t v_result_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; double v___x_3262_; lean_object* v_data_3263_; 
v_result_3259_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_fst_3236_);
v___x_3260_ = lean_box(v_result_3259_);
v___x_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
v___x_3262_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3223_);
lean_inc_ref(v___x_3261_);
lean_inc(v_cls_3221_);
v_data_3263_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3263_, 0, v_cls_3221_);
lean_ctor_set(v_data_3263_, 1, v___x_3261_);
lean_ctor_set(v_data_3263_, 2, v_tag_3223_);
lean_ctor_set_float(v_data_3263_, sizeof(void*)*3, v___x_3262_);
lean_ctor_set_float(v_data_3263_, sizeof(void*)*3 + 8, v___x_3262_);
lean_ctor_set_uint8(v_data_3263_, sizeof(void*)*3 + 16, v_collapsed_3222_);
if (v___x_3255_ == 0)
{
lean_dec_ref_known(v___x_3261_, 1);
lean_dec(v_snd_3253_);
lean_dec(v_fst_3252_);
lean_dec_ref(v_tag_3223_);
lean_dec(v_cls_3221_);
v___y_3239_ = v_a_3258_;
v___y_3240_ = v___y_3257_;
v_data_3241_ = v_data_3263_;
goto v___jp_3238_;
}
else
{
lean_object* v_data_3264_; double v___x_3265_; double v___x_3266_; 
lean_dec_ref_known(v_data_3263_, 3);
v_data_3264_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3264_, 0, v_cls_3221_);
lean_ctor_set(v_data_3264_, 1, v___x_3261_);
lean_ctor_set(v_data_3264_, 2, v_tag_3223_);
v___x_3265_ = lean_unbox_float(v_fst_3252_);
lean_dec(v_fst_3252_);
lean_ctor_set_float(v_data_3264_, sizeof(void*)*3, v___x_3265_);
v___x_3266_ = lean_unbox_float(v_snd_3253_);
lean_dec(v_snd_3253_);
lean_ctor_set_float(v_data_3264_, sizeof(void*)*3 + 8, v___x_3266_);
lean_ctor_set_uint8(v_data_3264_, sizeof(void*)*3 + 16, v_collapsed_3222_);
v___y_3239_ = v_a_3258_;
v___y_3240_ = v___y_3257_;
v_data_3241_ = v_data_3264_;
goto v___jp_3238_;
}
}
v___jp_3267_:
{
lean_object* v_ref_3268_; lean_object* v___x_3269_; 
v_ref_3268_ = lean_ctor_get(v___y_3233_, 2);
lean_inc(v___y_3234_);
lean_inc_ref(v___y_3233_);
lean_inc(v___y_3232_);
lean_inc_ref(v___y_3231_);
lean_inc(v___y_3230_);
lean_inc_ref(v___y_3229_);
lean_inc(v_fst_3236_);
v___x_3269_ = lean_apply_8(v_msg_3227_, v_fst_3236_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, lean_box(0));
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3269_, 1);
v___y_3257_ = v_ref_3268_;
v_a_3258_ = v_a_3270_;
goto v___jp_3256_;
}
else
{
lean_object* v___x_3271_; 
lean_dec_ref_known(v___x_3269_, 1);
v___x_3271_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_3257_ = v_ref_3268_;
v_a_3258_ = v___x_3271_;
goto v___jp_3256_;
}
}
v___jp_3272_:
{
if (v_clsEnabled_3225_ == 0)
{
if (v___y_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v_traceState_3275_; lean_object* v_env_3276_; lean_object* v_nextMacroScope_3277_; lean_object* v_ngen_3278_; lean_object* v_auxDeclNGen_3279_; lean_object* v_cache_3280_; lean_object* v_recordedDeps_3281_; lean_object* v_messages_3282_; lean_object* v_infoState_3283_; lean_object* v_snapshotTasks_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v_snd_3253_);
lean_dec(v_fst_3252_);
lean_dec_ref(v_msg_3227_);
lean_dec_ref(v_tag_3223_);
lean_dec(v_cls_3221_);
v___x_3274_ = lean_st_ref_take(v___y_3234_);
v_traceState_3275_ = lean_ctor_get(v___x_3274_, 4);
v_env_3276_ = lean_ctor_get(v___x_3274_, 0);
v_nextMacroScope_3277_ = lean_ctor_get(v___x_3274_, 1);
v_ngen_3278_ = lean_ctor_get(v___x_3274_, 2);
v_auxDeclNGen_3279_ = lean_ctor_get(v___x_3274_, 3);
v_cache_3280_ = lean_ctor_get(v___x_3274_, 5);
v_recordedDeps_3281_ = lean_ctor_get(v___x_3274_, 6);
v_messages_3282_ = lean_ctor_get(v___x_3274_, 7);
v_infoState_3283_ = lean_ctor_get(v___x_3274_, 8);
v_snapshotTasks_3284_ = lean_ctor_get(v___x_3274_, 9);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3286_ = v___x_3274_;
v_isShared_3287_ = v_isSharedCheck_3303_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_snapshotTasks_3284_);
lean_inc(v_infoState_3283_);
lean_inc(v_messages_3282_);
lean_inc(v_recordedDeps_3281_);
lean_inc(v_cache_3280_);
lean_inc(v_traceState_3275_);
lean_inc(v_auxDeclNGen_3279_);
lean_inc(v_ngen_3278_);
lean_inc(v_nextMacroScope_3277_);
lean_inc(v_env_3276_);
lean_dec(v___x_3274_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3303_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
uint64_t v_tid_3288_; lean_object* v_traces_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3302_; 
v_tid_3288_ = lean_ctor_get_uint64(v_traceState_3275_, sizeof(void*)*1);
v_traces_3289_ = lean_ctor_get(v_traceState_3275_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_traceState_3275_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3291_ = v_traceState_3275_;
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_traces_3289_);
lean_dec(v_traceState_3275_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3226_, v_traces_3289_);
lean_dec_ref(v_traces_3289_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3293_);
lean_ctor_set_uint64(v_reuseFailAlloc_3301_, sizeof(void*)*1, v_tid_3288_);
v___x_3295_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 4, v___x_3295_);
v___x_3297_ = v___x_3286_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_env_3276_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_nextMacroScope_3277_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_ngen_3278_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v_auxDeclNGen_3279_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3300_, 5, v_cache_3280_);
lean_ctor_set(v_reuseFailAlloc_3300_, 6, v_recordedDeps_3281_);
lean_ctor_set(v_reuseFailAlloc_3300_, 7, v_messages_3282_);
lean_ctor_set(v_reuseFailAlloc_3300_, 8, v_infoState_3283_);
lean_ctor_set(v_reuseFailAlloc_3300_, 9, v_snapshotTasks_3284_);
v___x_3297_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = lean_st_ref_put(v___y_3234_, v___x_3297_);
v___x_3299_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3236_);
return v___x_3299_;
}
}
}
}
}
else
{
goto v___jp_3267_;
}
}
else
{
goto v___jp_3267_;
}
}
v___jp_3304_:
{
double v___x_3306_; double v___x_3307_; double v___x_3308_; uint8_t v___x_3309_; 
v___x_3306_ = lean_unbox_float(v_snd_3253_);
v___x_3307_ = lean_unbox_float(v_fst_3252_);
v___x_3308_ = lean_float_sub(v___x_3306_, v___x_3307_);
v___x_3309_ = lean_float_decLt(v___y_3305_, v___x_3308_);
v___y_3273_ = v___x_3309_;
goto v___jp_3272_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3221_ = stack[0].m_obj;
uint8_t v_collapsed_3222_ = stack[1].m_num;
lean_object* v_tag_3223_ = stack[2].m_obj;
lean_object* v_opts_3224_ = stack[3].m_obj;
uint8_t v_clsEnabled_3225_ = stack[4].m_num;
lean_object* v_oldTraces_3226_ = stack[5].m_obj;
lean_object* v_msg_3227_ = stack[6].m_obj;
lean_object* v_resStartStop_3228_ = stack[7].m_obj;
lean_object* v___y_3229_ = stack[8].m_obj;
lean_object* v___y_3230_ = stack[9].m_obj;
lean_object* v___y_3231_ = stack[10].m_obj;
lean_object* v___y_3232_ = stack[11].m_obj;
lean_object* v___y_3233_ = stack[12].m_obj;
lean_object* v___y_3234_ = stack[13].m_obj;
lean_object* v_res_3320_;
v_res_3320_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3221_, v_collapsed_3222_, v_tag_3223_, v_opts_3224_, v_clsEnabled_3225_, v_oldTraces_3226_, v_msg_3227_, v_resStartStop_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
stack->m_obj
 = v_res_3320_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v_cls_3321_, lean_object* v_collapsed_3322_, lean_object* v_tag_3323_, lean_object* v_opts_3324_, lean_object* v_clsEnabled_3325_, lean_object* v_oldTraces_3326_, lean_object* v_msg_3327_, lean_object* v_resStartStop_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
uint8_t v_collapsed_boxed_3336_; uint8_t v_clsEnabled_boxed_3337_; lean_object* v_res_3338_; 
v_collapsed_boxed_3336_ = lean_unbox(v_collapsed_3322_);
v_clsEnabled_boxed_3337_ = lean_unbox(v_clsEnabled_3325_);
v_res_3338_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3321_, v_collapsed_boxed_3336_, v_tag_3323_, v_opts_3324_, v_clsEnabled_boxed_3337_, v_oldTraces_3326_, v_msg_3327_, v_resStartStop_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v_opts_3324_);
return v_res_3338_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v___x_3339_, lean_object* v_as_3340_, size_t v_i_3341_, size_t v_stop_3342_, lean_object* v_b_3343_){
_start:
{
lean_object* v___y_3345_; uint8_t v___x_3349_; 
v___x_3349_ = lean_usize_dec_eq(v_i_3341_, v_stop_3342_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3350_ = lean_array_uget_borrowed(v_as_3340_, v_i_3341_);
v___x_3351_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v___x_3339_, v___x_3350_);
if (v___x_3351_ == 0)
{
v___y_3345_ = v_b_3343_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3352_; 
lean_inc(v___x_3350_);
v___x_3352_ = lean_array_push(v_b_3343_, v___x_3350_);
v___y_3345_ = v___x_3352_;
goto v___jp_3344_;
}
}
else
{
return v_b_3343_;
}
v___jp_3344_:
{
size_t v___x_3346_; size_t v___x_3347_; 
v___x_3346_ = ((size_t)1ULL);
v___x_3347_ = lean_usize_add(v_i_3341_, v___x_3346_);
v_i_3341_ = v___x_3347_;
v_b_3343_ = v___y_3345_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3339_ = stack[0].m_obj;
lean_object* v_as_3340_ = stack[1].m_obj;
size_t v_i_3341_ = stack[2].m_num;
size_t v_stop_3342_ = stack[3].m_num;
lean_object* v_b_3343_ = stack[4].m_obj;
lean_object* v_res_3353_;
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3339_, v_as_3340_, v_i_3341_, v_stop_3342_, v_b_3343_);
stack->m_obj
 = v_res_3353_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v___x_3354_, lean_object* v_as_3355_, lean_object* v_i_3356_, lean_object* v_stop_3357_, lean_object* v_b_3358_){
_start:
{
size_t v_i_boxed_3359_; size_t v_stop_boxed_3360_; lean_object* v_res_3361_; 
v_i_boxed_3359_ = lean_unbox_usize(v_i_3356_);
lean_dec(v_i_3356_);
v_stop_boxed_3360_ = lean_unbox_usize(v_stop_3357_);
lean_dec(v_stop_3357_);
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3354_, v_as_3355_, v_i_boxed_3359_, v_stop_boxed_3360_, v_b_3358_);
lean_dec_ref(v_as_3355_);
lean_dec_ref(v___x_3354_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
if (lean_obj_tag(v_a_3362_) == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = l_List_reverse___redArg(v_a_3363_);
return v___x_3364_;
}
else
{
lean_object* v_head_3365_; lean_object* v_tail_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3375_; 
v_head_3365_ = lean_ctor_get(v_a_3362_, 0);
v_tail_3366_ = lean_ctor_get(v_a_3362_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_a_3362_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3368_ = v_a_3362_;
v_isShared_3369_ = v_isSharedCheck_3375_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_tail_3366_);
lean_inc(v_head_3365_);
lean_dec(v_a_3362_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3375_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = l_Lean_MessageData_ofExpr(v_head_3365_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v_a_3363_);
lean_ctor_set(v___x_3368_, 0, v___x_3370_);
v___x_3372_ = v___x_3368_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_a_3363_);
v___x_3372_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
v_a_3362_ = v_tail_3366_;
v_a_3363_ = v___x_3372_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3379_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3380_ = lean_unsigned_to_nat(6u);
v___x_3381_ = lean_unsigned_to_nat(108u);
v___x_3382_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3383_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3384_ = l_mkPanicMessageWithDecl(v___x_3383_, v___x_3382_, v___x_3381_, v___x_3380_, v___x_3379_);
return v___x_3384_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
return v___x_3387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
return v___x_3390_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3393_ = l_Lean_stringToMessageData(v___x_3392_);
return v___x_3393_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3395_ = l_Lean_stringToMessageData(v___x_3394_);
return v___x_3395_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = lean_box(0);
v___x_3397_ = lean_unsigned_to_nat(16u);
v___x_3398_ = lean_mk_array(v___x_3397_, v___x_3396_);
return v___x_3398_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3415_, lean_object* v_us_3416_, lean_object* v_xs_3417_, lean_object* v___x_3418_, lean_object* v___x_3419_, lean_object* v_ctorName_3420_, lean_object* v___x_3421_, lean_object* v___f_3422_, lean_object* v_insts_3423_, lean_object* v_localInst2Index_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3432_; lean_object* v_type_3433_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; uint8_t v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; uint8_t v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v_val_3570_; lean_object* v___y_3597_; lean_object* v___y_3608_; lean_object* v___x_3618_; lean_object* v_env_3619_; uint8_t v___x_3620_; uint8_t v___x_3621_; 
lean_inc(v_us_3416_);
lean_inc(v_inductiveTypeName_3415_);
v___x_3432_ = l_Lean_Expr_const___override(v_inductiveTypeName_3415_, v_us_3416_);
v_type_3433_ = l_Lean_mkAppN(v___x_3432_, v_xs_3417_);
v___x_3618_ = lean_st_ref_get(v___y_3430_);
v_env_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc_ref(v_env_3619_);
lean_dec(v___x_3618_);
v___x_3620_ = l_Lean_isStructure(v_env_3619_, v_inductiveTypeName_3415_);
v___x_3621_ = 1;
if (v___x_3620_ == 0)
{
lean_object* v_toCold_3622_; lean_object* v_options_3623_; lean_object* v_inheritedTraceOptions_3624_; uint8_t v_hasTrace_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_dec_ref(v___f_3422_);
v_toCold_3622_ = lean_ctor_get(v___y_3429_, 0);
v_options_3623_ = lean_ctor_get(v_toCold_3622_, 2);
v_inheritedTraceOptions_3624_ = lean_ctor_get(v_toCold_3622_, 11);
v_hasTrace_3625_ = lean_ctor_get_uint8(v_options_3623_, sizeof(void*)*1);
lean_inc(v_ctorName_3420_);
v___x_3626_ = l_Lean_Expr_const___override(v_ctorName_3420_, v_us_3416_);
v___x_3627_ = l_Lean_mkAppN(v___x_3626_, v___x_3421_);
if (v_hasTrace_3625_ == 0)
{
lean_object* v___x_3628_; 
lean_dec(v_ctorName_3420_);
lean_inc(v___y_3430_);
lean_inc_ref(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc_ref(v___y_3427_);
lean_inc_ref(v___x_3627_);
v___x_3628_ = lean_infer_type(v___x_3627_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; lean_object* v___x_3632_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v___x_3630_ = lean_box(0);
v___x_3631_ = 0;
v___x_3632_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3629_, v___x_3630_, v___x_3631_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v_snd_3634_; lean_object* v_fst_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3678_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v_snd_3634_ = lean_ctor_get(v_a_3633_, 1);
v_fst_3635_ = lean_ctor_get(v_a_3633_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3633_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3637_ = v_a_3633_;
v_isShared_3638_ = v_isSharedCheck_3678_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_snd_3634_);
lean_inc(v_fst_3635_);
lean_dec(v_a_3633_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3678_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v_snd_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3676_; 
v_snd_3639_ = lean_ctor_get(v_snd_3634_, 1);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_snd_3634_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v_snd_3634_, 0);
lean_dec(v_unused_3677_);
v___x_3641_ = v_snd_3634_;
v_isShared_3642_ = v_isSharedCheck_3676_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_snd_3639_);
lean_dec(v_snd_3634_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3676_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; 
lean_inc(v_snd_3639_);
lean_inc_ref(v_type_3433_);
v___x_3643_ = l_Lean_Meta_isExprDefEq(v_type_3433_, v_snd_3639_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; uint8_t v___x_3645_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3645_ = lean_unbox(v_a_3644_);
lean_dec(v_a_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
lean_dec(v_fst_3635_);
lean_dec_ref(v___x_3627_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v___x_3646_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3647_ = l_Lean_indentExpr(v_type_3433_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 7);
lean_ctor_set(v___x_3641_, 1, v___x_3647_);
lean_ctor_set(v___x_3641_, 0, v___x_3646_);
v___x_3649_ = v___x_3641_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3650_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 7);
lean_ctor_set(v___x_3637_, 1, v___x_3650_);
lean_ctor_set(v___x_3637_, 0, v___x_3649_);
v___x_3652_ = v___x_3637_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3649_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v___x_3653_ = l_Lean_indentExpr(v_snd_3639_);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3654_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
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
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_del_object(v___x_3641_);
lean_dec(v_snd_3639_);
lean_del_object(v___x_3637_);
v___x_3666_ = lean_box(0);
v___x_3667_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3627_, v_fst_3635_, v___x_3666_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v_fst_3635_);
v___y_3608_ = v___x_3667_;
goto v___jp_3607_;
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_del_object(v___x_3641_);
lean_dec(v_snd_3639_);
lean_del_object(v___x_3637_);
lean_dec(v_fst_3635_);
lean_dec_ref(v___x_3627_);
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v_a_3668_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3643_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3643_);
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
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec_ref(v___x_3627_);
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v_a_3679_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3632_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3632_);
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
else
{
lean_dec_ref(v___x_3627_);
v___y_3608_ = v___x_3628_;
goto v___jp_3607_;
}
}
else
{
lean_object* v___x_3687_; lean_object* v___f_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v_a_3696_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v_a_3711_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v_a_3729_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v_a_3741_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; 
v___x_3687_ = lean_box(v___x_3620_);
v___f_3688_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3688_, 0, v_ctorName_3420_);
lean_closure_set(v___f_3688_, 1, v___x_3687_);
v___x_3689_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3690_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3691_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3624_, v_options_3623_, v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3839_; uint8_t v___x_3840_; 
v___x_3839_ = l_Lean_trace_profiler;
v___x_3840_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3623_, v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
lean_dec_ref(v___f_3688_);
lean_inc(v___y_3430_);
lean_inc_ref(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc_ref(v___y_3427_);
lean_inc_ref(v___x_3627_);
v___x_3841_ = lean_infer_type(v___x_3627_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; lean_object* v___x_3845_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
v___x_3843_ = lean_box(0);
v___x_3844_ = 0;
v___x_3845_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3842_, v___x_3843_, v___x_3844_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v_snd_3847_; lean_object* v_fst_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3891_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v_snd_3847_ = lean_ctor_get(v_a_3846_, 1);
v_fst_3848_ = lean_ctor_get(v_a_3846_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_a_3846_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3850_ = v_a_3846_;
v_isShared_3851_ = v_isSharedCheck_3891_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_snd_3847_);
lean_inc(v_fst_3848_);
lean_dec(v_a_3846_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3891_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v_snd_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3889_; 
v_snd_3852_ = lean_ctor_get(v_snd_3847_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_snd_3847_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v_snd_3847_, 0);
lean_dec(v_unused_3890_);
v___x_3854_ = v_snd_3847_;
v_isShared_3855_ = v_isSharedCheck_3889_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_snd_3852_);
lean_dec(v_snd_3847_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3889_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; 
lean_inc(v_snd_3852_);
lean_inc_ref(v_type_3433_);
v___x_3856_ = l_Lean_Meta_isExprDefEq(v_type_3433_, v_snd_3852_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; uint8_t v___x_3858_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = lean_unbox(v_a_3857_);
lean_dec(v_a_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3862_; 
lean_dec(v_fst_3848_);
lean_dec_ref(v___x_3627_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v___x_3859_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3860_ = l_Lean_indentExpr(v_type_3433_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set_tag(v___x_3854_, 7);
lean_ctor_set(v___x_3854_, 1, v___x_3860_);
lean_ctor_set(v___x_3854_, 0, v___x_3859_);
v___x_3862_ = v___x_3854_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; lean_object* v___x_3865_; 
v___x_3863_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3851_ == 0)
{
lean_ctor_set_tag(v___x_3850_, 7);
lean_ctor_set(v___x_3850_, 1, v___x_3863_);
lean_ctor_set(v___x_3850_, 0, v___x_3862_);
v___x_3865_ = v___x_3850_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
v___x_3866_ = l_Lean_indentExpr(v_snd_3852_);
v___x_3867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3865_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3867_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3868_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3868_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_del_object(v___x_3854_);
lean_dec(v_snd_3852_);
lean_del_object(v___x_3850_);
v___x_3879_ = lean_box(0);
v___x_3880_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3627_, v_fst_3848_, v___x_3879_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v_fst_3848_);
v___y_3608_ = v___x_3880_;
goto v___jp_3607_;
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_del_object(v___x_3854_);
lean_dec(v_snd_3852_);
lean_del_object(v___x_3850_);
lean_dec(v_fst_3848_);
lean_dec_ref(v___x_3627_);
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v_a_3881_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3856_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3856_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v___x_3627_);
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v_a_3892_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3845_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3845_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_dec_ref(v___x_3627_);
v___y_3608_ = v___x_3841_;
goto v___jp_3607_;
}
}
else
{
goto v___jp_3756_;
}
}
else
{
goto v___jp_3756_;
}
v___jp_3693_:
{
lean_object* v___x_3697_; double v___x_3698_; double v___x_3699_; double v___x_3700_; double v___x_3701_; double v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3697_ = lean_io_mono_nanos_now();
v___x_3698_ = lean_float_of_nat(v___y_3695_);
v___x_3699_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3700_ = lean_float_div(v___x_3698_, v___x_3699_);
v___x_3701_ = lean_float_of_nat(v___x_3697_);
v___x_3702_ = lean_float_div(v___x_3701_, v___x_3699_);
v___x_3703_ = lean_box_float(v___x_3700_);
v___x_3704_ = lean_box_float(v___x_3702_);
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3706_, 0, v_a_3696_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3689_, v___x_3621_, v___x_3690_, v_options_3623_, v___x_3692_, v___y_3694_, v___f_3688_, v___x_3706_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v___y_3608_ = v___x_3707_;
goto v___jp_3607_;
}
v___jp_3708_:
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v_a_3711_);
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
v_a_3696_ = v___x_3712_;
goto v___jp_3693_;
}
v___jp_3713_:
{
if (lean_obj_tag(v___y_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
v_a_3717_ = lean_ctor_get(v___y_3716_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___y_3716_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___y_3716_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___y_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
lean_ctor_set_tag(v___x_3719_, 1);
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
v___y_3694_ = v___y_3714_;
v___y_3695_ = v___y_3715_;
v_a_3696_ = v___x_3722_;
goto v___jp_3693_;
}
}
}
else
{
lean_object* v_a_3725_; 
v_a_3725_ = lean_ctor_get(v___y_3716_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___y_3716_, 1);
v___y_3709_ = v___y_3714_;
v___y_3710_ = v___y_3715_;
v_a_3711_ = v_a_3725_;
goto v___jp_3708_;
}
}
v___jp_3726_:
{
lean_object* v___x_3730_; double v___x_3731_; double v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3730_ = lean_io_get_num_heartbeats();
v___x_3731_ = lean_float_of_nat(v___y_3728_);
v___x_3732_ = lean_float_of_nat(v___x_3730_);
v___x_3733_ = lean_box_float(v___x_3731_);
v___x_3734_ = lean_box_float(v___x_3732_);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v_a_3729_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3689_, v___x_3621_, v___x_3690_, v_options_3623_, v___x_3692_, v___y_3727_, v___f_3688_, v___x_3736_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v___y_3608_ = v___x_3737_;
goto v___jp_3607_;
}
v___jp_3738_:
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v_a_3741_);
v___y_3727_ = v___y_3739_;
v___y_3728_ = v___y_3740_;
v_a_3729_ = v___x_3742_;
goto v___jp_3726_;
}
v___jp_3743_:
{
if (lean_obj_tag(v___y_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v_a_3747_ = lean_ctor_get(v___y_3746_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___y_3746_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___y_3746_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___y_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 1);
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
v___y_3727_ = v___y_3744_;
v___y_3728_ = v___y_3745_;
v_a_3729_ = v___x_3752_;
goto v___jp_3726_;
}
}
}
else
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___y_3746_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___y_3746_, 1);
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___y_3745_;
v_a_3741_ = v_a_3755_;
goto v___jp_3738_;
}
}
v___jp_3756_:
{
lean_object* v___x_3757_; lean_object* v_a_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v___x_3757_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3430_);
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref(v___x_3757_);
v___x_3759_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3760_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3623_, v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = lean_io_mono_nanos_now();
lean_inc(v___y_3430_);
lean_inc_ref(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc_ref(v___y_3427_);
lean_inc_ref(v___x_3627_);
v___x_3762_ = lean_infer_type(v___x_3627_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref_known(v___x_3762_, 1);
v___x_3764_ = lean_box(0);
v___x_3765_ = 0;
v___x_3766_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3763_, v___x_3764_, v___x_3765_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v_snd_3768_; lean_object* v_fst_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3798_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v_snd_3768_ = lean_ctor_get(v_a_3767_, 1);
v_fst_3769_ = lean_ctor_get(v_a_3767_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_a_3767_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3771_ = v_a_3767_;
v_isShared_3772_ = v_isSharedCheck_3798_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_snd_3768_);
lean_inc(v_fst_3769_);
lean_dec(v_a_3767_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3798_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v_snd_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3796_; 
v_snd_3773_ = lean_ctor_get(v_snd_3768_, 1);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_snd_3768_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v_snd_3768_, 0);
lean_dec(v_unused_3797_);
v___x_3775_ = v_snd_3768_;
v_isShared_3776_ = v_isSharedCheck_3796_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_snd_3773_);
lean_dec(v_snd_3768_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3796_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3777_; 
lean_inc(v_snd_3773_);
lean_inc_ref(v_type_3433_);
v___x_3777_ = l_Lean_Meta_isExprDefEq(v_type_3433_, v_snd_3773_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; uint8_t v___x_3779_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
v___x_3779_ = lean_unbox(v_a_3778_);
lean_dec(v_a_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
lean_dec(v_fst_3769_);
lean_dec_ref(v___x_3627_);
v___x_3780_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3433_);
v___x_3781_ = l_Lean_indentExpr(v_type_3433_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set_tag(v___x_3775_, 7);
lean_ctor_set(v___x_3775_, 1, v___x_3781_);
lean_ctor_set(v___x_3775_, 0, v___x_3780_);
v___x_3783_ = v___x_3775_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3784_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3772_ == 0)
{
lean_ctor_set_tag(v___x_3771_, 7);
lean_ctor_set(v___x_3771_, 1, v___x_3784_);
lean_ctor_set(v___x_3771_, 0, v___x_3783_);
v___x_3786_ = v___x_3771_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v_a_3790_; 
v___x_3787_ = l_Lean_indentExpr(v_snd_3773_);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3788_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___y_3709_ = v_a_3758_;
v___y_3710_ = v___x_3761_;
v_a_3711_ = v_a_3790_;
goto v___jp_3708_;
}
}
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_del_object(v___x_3775_);
lean_dec(v_snd_3773_);
lean_del_object(v___x_3771_);
v___x_3793_ = lean_box(0);
v___x_3794_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3627_, v_fst_3769_, v___x_3793_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v_fst_3769_);
v___y_3714_ = v_a_3758_;
v___y_3715_ = v___x_3761_;
v___y_3716_ = v___x_3794_;
goto v___jp_3713_;
}
}
else
{
lean_object* v_a_3795_; 
lean_del_object(v___x_3775_);
lean_dec(v_snd_3773_);
lean_del_object(v___x_3771_);
lean_dec(v_fst_3769_);
lean_dec_ref(v___x_3627_);
v_a_3795_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3777_, 1);
v___y_3709_ = v_a_3758_;
v___y_3710_ = v___x_3761_;
v_a_3711_ = v_a_3795_;
goto v___jp_3708_;
}
}
}
}
else
{
lean_object* v_a_3799_; 
lean_dec_ref(v___x_3627_);
v_a_3799_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3766_, 1);
v___y_3709_ = v_a_3758_;
v___y_3710_ = v___x_3761_;
v_a_3711_ = v_a_3799_;
goto v___jp_3708_;
}
}
else
{
lean_dec_ref(v___x_3627_);
v___y_3714_ = v_a_3758_;
v___y_3715_ = v___x_3761_;
v___y_3716_ = v___x_3762_;
goto v___jp_3713_;
}
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3430_);
lean_inc_ref(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc_ref(v___y_3427_);
lean_inc_ref(v___x_3627_);
v___x_3801_ = lean_infer_type(v___x_3627_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; lean_object* v___x_3805_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3803_ = lean_box(0);
v___x_3804_ = 0;
v___x_3805_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3802_, v___x_3803_, v___x_3804_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v_snd_3807_; lean_object* v_fst_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3837_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
v_snd_3807_ = lean_ctor_get(v_a_3806_, 1);
v_fst_3808_ = lean_ctor_get(v_a_3806_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_a_3806_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3810_ = v_a_3806_;
v_isShared_3811_ = v_isSharedCheck_3837_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_snd_3807_);
lean_inc(v_fst_3808_);
lean_dec(v_a_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3837_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v_snd_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3835_; 
v_snd_3812_ = lean_ctor_get(v_snd_3807_, 1);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_snd_3807_);
if (v_isSharedCheck_3835_ == 0)
{
lean_object* v_unused_3836_; 
v_unused_3836_ = lean_ctor_get(v_snd_3807_, 0);
lean_dec(v_unused_3836_);
v___x_3814_ = v_snd_3807_;
v_isShared_3815_ = v_isSharedCheck_3835_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_snd_3812_);
lean_dec(v_snd_3807_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3835_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; 
lean_inc(v_snd_3812_);
lean_inc_ref(v_type_3433_);
v___x_3816_ = l_Lean_Meta_isExprDefEq(v_type_3433_, v_snd_3812_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; uint8_t v___x_3818_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = lean_unbox(v_a_3817_);
lean_dec(v_a_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3822_; 
lean_dec(v_fst_3808_);
lean_dec_ref(v___x_3627_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3433_);
v___x_3820_ = l_Lean_indentExpr(v_type_3433_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set_tag(v___x_3814_, 7);
lean_ctor_set(v___x_3814_, 1, v___x_3820_);
lean_ctor_set(v___x_3814_, 0, v___x_3819_);
v___x_3822_ = v___x_3814_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3823_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3811_ == 0)
{
lean_ctor_set_tag(v___x_3810_, 7);
lean_ctor_set(v___x_3810_, 1, v___x_3823_);
lean_ctor_set(v___x_3810_, 0, v___x_3822_);
v___x_3825_ = v___x_3810_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v_a_3829_; 
v___x_3826_ = l_Lean_indentExpr(v_snd_3812_);
v___x_3827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3825_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
v___x_3828_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3827_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
v___y_3739_ = v_a_3758_;
v___y_3740_ = v___x_3800_;
v_a_3741_ = v_a_3829_;
goto v___jp_3738_;
}
}
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_del_object(v___x_3814_);
lean_dec(v_snd_3812_);
lean_del_object(v___x_3810_);
v___x_3832_ = lean_box(0);
v___x_3833_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3627_, v_fst_3808_, v___x_3832_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v_fst_3808_);
v___y_3744_ = v_a_3758_;
v___y_3745_ = v___x_3800_;
v___y_3746_ = v___x_3833_;
goto v___jp_3743_;
}
}
else
{
lean_object* v_a_3834_; 
lean_del_object(v___x_3814_);
lean_dec(v_snd_3812_);
lean_del_object(v___x_3810_);
lean_dec(v_fst_3808_);
lean_dec_ref(v___x_3627_);
v_a_3834_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3816_, 1);
v___y_3739_ = v_a_3758_;
v___y_3740_ = v___x_3800_;
v_a_3741_ = v_a_3834_;
goto v___jp_3738_;
}
}
}
}
else
{
lean_object* v_a_3838_; 
lean_dec_ref(v___x_3627_);
v_a_3838_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3805_, 1);
v___y_3739_ = v_a_3758_;
v___y_3740_ = v___x_3800_;
v_a_3741_ = v_a_3838_;
goto v___jp_3738_;
}
}
else
{
lean_dec_ref(v___x_3627_);
v___y_3744_ = v_a_3758_;
v___y_3745_ = v___x_3800_;
v___y_3746_ = v___x_3801_;
goto v___jp_3743_;
}
}
}
}
}
else
{
lean_object* v_toCold_3900_; lean_object* v_options_3901_; uint8_t v_hasTrace_3902_; 
lean_dec(v_ctorName_3420_);
lean_dec(v_us_3416_);
v_toCold_3900_ = lean_ctor_get(v___y_3429_, 0);
v_options_3901_ = lean_ctor_get(v_toCold_3900_, 2);
v_hasTrace_3902_ = lean_ctor_get_uint8(v_options_3901_, sizeof(void*)*1);
if (v_hasTrace_3902_ == 0)
{
lean_object* v_ref_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref(v___f_3422_);
v_ref_3903_ = lean_ctor_get(v___y_3429_, 2);
v___x_3904_ = l_Lean_SourceInfo_fromRef(v_ref_3903_, v_hasTrace_3902_);
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3906_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3904_);
v___x_3907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3904_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = l_Lean_Syntax_node1(v___x_3904_, v___x_3905_, v___x_3907_);
lean_inc_ref(v_type_3433_);
v___x_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3909_, 0, v_type_3433_);
v___x_3910_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3910_, 0, v___x_3908_);
lean_closure_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3910_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v___y_3597_ = v___x_3911_;
goto v___jp_3596_;
}
else
{
lean_object* v_ref_3912_; lean_object* v_inheritedTraceOptions_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v_a_3921_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v_a_3936_; 
v_ref_3912_ = lean_ctor_get(v___y_3429_, 2);
v_inheritedTraceOptions_3913_ = lean_ctor_get(v_toCold_3900_, 11);
v___x_3914_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3915_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3916_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3913_, v_options_3901_, v___x_3916_);
if (v___x_3917_ == 0)
{
lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4009_ = l_Lean_trace_profiler;
v___x_4010_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3901_, v___x_4009_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec_ref(v___f_3422_);
v___x_4011_ = l_Lean_SourceInfo_fromRef(v_ref_3912_, v___x_4010_);
v___x_4012_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_4013_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_4011_);
v___x_4014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4011_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = l_Lean_Syntax_node1(v___x_4011_, v___x_4012_, v___x_4014_);
lean_inc_ref(v_type_3433_);
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v_type_3433_);
v___x_4017_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_4017_, 0, v___x_4015_);
lean_closure_set(v___x_4017_, 1, v___x_4016_);
v___x_4018_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_4017_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v___y_3597_ = v___x_4018_;
goto v___jp_3596_;
}
else
{
goto v___jp_3945_;
}
}
else
{
goto v___jp_3945_;
}
v___jp_3918_:
{
lean_object* v___x_3922_; double v___x_3923_; double v___x_3924_; double v___x_3925_; double v___x_3926_; double v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3922_ = lean_io_mono_nanos_now();
v___x_3923_ = lean_float_of_nat(v___y_3919_);
v___x_3924_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3925_ = lean_float_div(v___x_3923_, v___x_3924_);
v___x_3926_ = lean_float_of_nat(v___x_3922_);
v___x_3927_ = lean_float_div(v___x_3926_, v___x_3924_);
v___x_3928_ = lean_box_float(v___x_3925_);
v___x_3929_ = lean_box_float(v___x_3927_);
v___x_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3931_, 0, v_a_3921_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3914_, v___x_3621_, v___x_3915_, v_options_3901_, v___x_3917_, v___y_3920_, v___f_3422_, v___x_3931_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v___y_3597_ = v___x_3932_;
goto v___jp_3596_;
}
v___jp_3933_:
{
lean_object* v___x_3937_; double v___x_3938_; double v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3937_ = lean_io_get_num_heartbeats();
v___x_3938_ = lean_float_of_nat(v___y_3934_);
v___x_3939_ = lean_float_of_nat(v___x_3937_);
v___x_3940_ = lean_box_float(v___x_3938_);
v___x_3941_ = lean_box_float(v___x_3939_);
v___x_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v_a_3936_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3914_, v___x_3621_, v___x_3915_, v_options_3901_, v___x_3917_, v___y_3935_, v___f_3422_, v___x_3943_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v___y_3597_ = v___x_3944_;
goto v___jp_3596_;
}
v___jp_3945_:
{
lean_object* v___x_3946_; lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_4008_; 
v___x_3946_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3430_);
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_4008_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_4008_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3951_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3952_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3901_, v___x_3951_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3953_ = lean_io_mono_nanos_now();
v___x_3954_ = l_Lean_SourceInfo_fromRef(v_ref_3912_, v___x_3952_);
v___x_3955_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3954_);
v___x_3957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3954_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = l_Lean_Syntax_node1(v___x_3954_, v___x_3955_, v___x_3957_);
lean_inc_ref(v_type_3433_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set_tag(v___x_3949_, 1);
lean_ctor_set(v___x_3949_, 0, v_type_3433_);
v___x_3960_ = v___x_3949_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_type_3433_);
v___x_3960_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3961_, 0, v___x_3958_);
lean_closure_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3961_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
lean_ctor_set_tag(v___x_3965_, 1);
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
v___y_3919_ = v___x_3953_;
v___y_3920_ = v_a_3947_;
v_a_3921_ = v___x_3968_;
goto v___jp_3918_;
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_a_3971_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3962_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3962_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
lean_ctor_set_tag(v___x_3973_, 0);
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
v___y_3919_ = v___x_3953_;
v___y_3920_ = v_a_3947_;
v_a_3921_ = v___x_3976_;
goto v___jp_3918_;
}
}
}
}
}
else
{
lean_object* v___x_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3980_ = lean_io_get_num_heartbeats();
v___x_3981_ = 0;
v___x_3982_ = l_Lean_SourceInfo_fromRef(v_ref_3912_, v___x_3981_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3984_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3982_);
v___x_3985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3982_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = l_Lean_Syntax_node1(v___x_3982_, v___x_3983_, v___x_3985_);
lean_inc_ref(v_type_3433_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set_tag(v___x_3949_, 1);
lean_ctor_set(v___x_3949_, 0, v_type_3433_);
v___x_3988_ = v___x_3949_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_type_3433_);
v___x_3988_ = v_reuseFailAlloc_4007_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3989_, 0, v___x_3986_);
lean_closure_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3989_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3990_) == 0)
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
lean_ctor_set_tag(v___x_3993_, 1);
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
v___y_3934_ = v___x_3980_;
v___y_3935_ = v_a_3947_;
v_a_3936_ = v___x_3996_;
goto v___jp_3933_;
}
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
v_a_3999_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3990_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3990_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set_tag(v___x_4001_, 0);
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
v___y_3934_ = v___x_3980_;
v___y_3935_ = v_a_3947_;
v_a_3936_ = v___x_4004_;
goto v___jp_3933_;
}
}
}
}
}
}
}
}
}
v___jp_3434_:
{
lean_object* v___x_3443_; uint8_t v___x_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3443_ = l_Array_append___redArg(v_xs_3417_, v___y_3437_);
lean_dec_ref(v___y_3437_);
v___x_3444_ = 0;
v___x_3445_ = 1;
v___x_3446_ = l_Lean_Meta_mkForallFVars(v___x_3443_, v_type_3433_, v___x_3444_, v___y_3438_, v___y_3438_, v___x_3445_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___x_3448_ = l_Lean_Meta_mkLambdaFVars(v___x_3443_, v___y_3436_, v___x_3444_, v___y_3438_, v___x_3444_, v___y_3438_, v___x_3445_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec_ref(v___x_3443_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3458_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3458_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3458_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v_a_3449_);
lean_ctor_set(v___x_3453_, 1, v___y_3435_);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v_a_3447_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3454_);
v___x_3456_ = v___x_3451_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_a_3447_);
lean_dec(v___y_3435_);
v_a_3459_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3448_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3448_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec_ref(v___x_3443_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
v_a_3467_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3446_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3446_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
v___jp_3475_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___y_3481_);
lean_ctor_set(v___x_3487_, 1, v___y_3486_);
lean_inc(v___y_3480_);
v___x_3488_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3480_, v___x_3487_, v___y_3485_, v___y_3484_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_dec_ref_known(v___x_3488_, 1);
v___y_3435_ = v___y_3476_;
v___y_3436_ = v___y_3477_;
v___y_3437_ = v___y_3482_;
v___y_3438_ = v___y_3483_;
v___y_3439_ = v___y_3485_;
v___y_3440_ = v___y_3484_;
v___y_3441_ = v___y_3478_;
v___y_3442_ = v___y_3479_;
goto v___jp_3434_;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec_ref(v___y_3482_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v_type_3433_);
lean_dec_ref(v_xs_3417_);
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
v___jp_3497_:
{
uint8_t v___x_3509_; 
v___x_3509_ = lean_nat_dec_eq(v___y_3499_, v___y_3508_);
lean_dec(v___y_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v_type_3433_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v___x_3510_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3511_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3510_, v___y_3504_, v___y_3507_, v___y_3506_, v___y_3505_, v___y_3501_, v___y_3502_);
return v___x_3511_;
}
else
{
lean_object* v_toCold_3512_; lean_object* v_options_3513_; uint8_t v_hasTrace_3514_; 
v_toCold_3512_ = lean_ctor_get(v___y_3501_, 0);
v_options_3513_ = lean_ctor_get(v_toCold_3512_, 2);
v_hasTrace_3514_ = lean_ctor_get_uint8(v_options_3513_, sizeof(void*)*1);
if (v_hasTrace_3514_ == 0)
{
lean_dec(v___y_3499_);
lean_dec(v___x_3418_);
v___y_3435_ = v___y_3498_;
v___y_3436_ = v___y_3500_;
v___y_3437_ = v___y_3503_;
v___y_3438_ = v___x_3509_;
v___y_3439_ = v___y_3506_;
v___y_3440_ = v___y_3505_;
v___y_3441_ = v___y_3501_;
v___y_3442_ = v___y_3502_;
goto v___jp_3434_;
}
else
{
lean_object* v_inheritedTraceOptions_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v_inheritedTraceOptions_3515_ = lean_ctor_get(v_toCold_3512_, 11);
v___x_3516_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3517_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3515_, v_options_3513_, v___x_3517_);
if (v___x_3518_ == 0)
{
lean_dec(v___y_3499_);
lean_dec(v___x_3418_);
v___y_3435_ = v___y_3498_;
v___y_3436_ = v___y_3500_;
v___y_3437_ = v___y_3503_;
v___y_3438_ = v___x_3509_;
v___y_3439_ = v___y_3506_;
v___y_3440_ = v___y_3505_;
v___y_3441_ = v___y_3501_;
v___y_3442_ = v___y_3502_;
goto v___jp_3434_;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v___x_3519_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3520_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3500_);
v___x_3521_ = l_Lean_inlineExpr(v___y_3500_, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3519_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_nat_dec_eq(v___y_3499_, v___x_3418_);
lean_dec(v___x_3418_);
lean_dec(v___y_3499_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3524_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3503_);
v___x_3525_ = lean_array_to_list(v___y_3503_);
v___x_3526_ = lean_box(0);
v___x_3527_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3525_, v___x_3526_);
v___x_3528_ = l_Lean_MessageData_ofList(v___x_3527_);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3524_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___y_3476_ = v___y_3498_;
v___y_3477_ = v___y_3500_;
v___y_3478_ = v___y_3501_;
v___y_3479_ = v___y_3502_;
v___y_3480_ = v___x_3516_;
v___y_3481_ = v___x_3522_;
v___y_3482_ = v___y_3503_;
v___y_3483_ = v___x_3509_;
v___y_3484_ = v___y_3505_;
v___y_3485_ = v___y_3506_;
v___y_3486_ = v___x_3531_;
goto v___jp_3475_;
}
else
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3476_ = v___y_3498_;
v___y_3477_ = v___y_3500_;
v___y_3478_ = v___y_3501_;
v___y_3479_ = v___y_3502_;
v___y_3480_ = v___x_3516_;
v___y_3481_ = v___x_3522_;
v___y_3482_ = v___y_3503_;
v___y_3483_ = v___x_3509_;
v___y_3484_ = v___y_3505_;
v___y_3485_ = v___y_3506_;
v___y_3486_ = v___x_3532_;
goto v___jp_3475_;
}
}
}
}
}
v___jp_3533_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_box(1);
lean_inc_ref(v___y_3535_);
v___x_3543_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3542_, v_localInst2Index_3424_, v___y_3535_);
v___x_3544_ = lean_array_get_size(v___y_3541_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_size_3545_; 
v_size_3545_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_size_3545_);
v___y_3498_ = v___x_3543_;
v___y_3499_ = v___x_3544_;
v___y_3500_ = v___y_3535_;
v___y_3501_ = v___y_3534_;
v___y_3502_ = v___y_3536_;
v___y_3503_ = v___y_3541_;
v___y_3504_ = v___y_3537_;
v___y_3505_ = v___y_3538_;
v___y_3506_ = v___y_3540_;
v___y_3507_ = v___y_3539_;
v___y_3508_ = v_size_3545_;
goto v___jp_3497_;
}
else
{
lean_inc(v___x_3418_);
v___y_3498_ = v___x_3543_;
v___y_3499_ = v___x_3544_;
v___y_3500_ = v___y_3535_;
v___y_3501_ = v___y_3534_;
v___y_3502_ = v___y_3536_;
v___y_3503_ = v___y_3541_;
v___y_3504_ = v___y_3537_;
v___y_3505_ = v___y_3538_;
v___y_3506_ = v___y_3540_;
v___y_3507_ = v___y_3539_;
v___y_3508_ = v___x_3418_;
goto v___jp_3497_;
}
}
v___jp_3546_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = lean_array_get_size(v_insts_3423_);
v___x_3555_ = lean_mk_empty_array_with_capacity(v___x_3418_);
v___x_3556_ = lean_nat_dec_lt(v___x_3418_, v___x_3554_);
if (v___x_3556_ == 0)
{
lean_dec(v___x_3419_);
v___y_3534_ = v___y_3552_;
v___y_3535_ = v___y_3547_;
v___y_3536_ = v___y_3553_;
v___y_3537_ = v___y_3548_;
v___y_3538_ = v___y_3551_;
v___y_3539_ = v___y_3549_;
v___y_3540_ = v___y_3550_;
v___y_3541_ = v___x_3555_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v_visitedExpr_3561_; uint8_t v___x_3562_; 
v___x_3557_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
lean_inc(v___x_3418_);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3418_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
lean_inc_ref(v___x_3555_);
v___x_3559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
lean_ctor_set(v___x_3559_, 1, v___x_3419_);
lean_ctor_set(v___x_3559_, 2, v___x_3555_);
lean_inc_ref(v___y_3547_);
v___x_3560_ = l_Lean_collectFVars(v___x_3559_, v___y_3547_);
v_visitedExpr_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_ref(v_visitedExpr_3561_);
lean_dec_ref(v___x_3560_);
v___x_3562_ = lean_nat_dec_le(v___x_3554_, v___x_3554_);
if (v___x_3562_ == 0)
{
if (v___x_3556_ == 0)
{
lean_dec_ref(v_visitedExpr_3561_);
v___y_3534_ = v___y_3552_;
v___y_3535_ = v___y_3547_;
v___y_3536_ = v___y_3553_;
v___y_3537_ = v___y_3548_;
v___y_3538_ = v___y_3551_;
v___y_3539_ = v___y_3549_;
v___y_3540_ = v___y_3550_;
v___y_3541_ = v___x_3555_;
goto v___jp_3533_;
}
else
{
size_t v___x_3563_; size_t v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = ((size_t)0ULL);
v___x_3564_ = lean_usize_of_nat(v___x_3554_);
v___x_3565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3561_, v_insts_3423_, v___x_3563_, v___x_3564_, v___x_3555_);
lean_dec_ref(v_visitedExpr_3561_);
v___y_3534_ = v___y_3552_;
v___y_3535_ = v___y_3547_;
v___y_3536_ = v___y_3553_;
v___y_3537_ = v___y_3548_;
v___y_3538_ = v___y_3551_;
v___y_3539_ = v___y_3549_;
v___y_3540_ = v___y_3550_;
v___y_3541_ = v___x_3565_;
goto v___jp_3533_;
}
}
else
{
size_t v___x_3566_; size_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = ((size_t)0ULL);
v___x_3567_ = lean_usize_of_nat(v___x_3554_);
v___x_3568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3561_, v_insts_3423_, v___x_3566_, v___x_3567_, v___x_3555_);
lean_dec_ref(v_visitedExpr_3561_);
v___y_3534_ = v___y_3552_;
v___y_3535_ = v___y_3547_;
v___y_3536_ = v___y_3553_;
v___y_3537_ = v___y_3548_;
v___y_3538_ = v___y_3551_;
v___y_3539_ = v___y_3549_;
v___y_3540_ = v___y_3550_;
v___y_3541_ = v___x_3568_;
goto v___jp_3533_;
}
}
}
v___jp_3569_:
{
lean_object* v___x_3571_; 
lean_inc_ref(v_val_3570_);
v___x_3571_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3570_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3572_; lean_object* v_a_3573_; uint8_t v___x_3574_; 
lean_dec_ref_known(v___x_3571_, 1);
v___x_3572_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3570_, v___y_3428_);
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = l_Lean_Expr_hasMVar(v_a_3573_);
if (v___x_3574_ == 0)
{
v___y_3547_ = v_a_3573_;
v___y_3548_ = v___y_3425_;
v___y_3549_ = v___y_3426_;
v___y_3550_ = v___y_3427_;
v___y_3551_ = v___y_3428_;
v___y_3552_ = v___y_3429_;
v___y_3553_ = v___y_3430_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v___x_3575_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13);
v___x_3576_ = lean_unsigned_to_nat(30u);
v___x_3577_ = l_Lean_inlineExprTrailing(v_a_3573_, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3575_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3578_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_val_3570_);
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v_a_3588_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3571_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3571_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
v___jp_3596_:
{
if (lean_obj_tag(v___y_3597_) == 0)
{
lean_object* v_a_3598_; 
v_a_3598_ = lean_ctor_get(v___y_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___y_3597_, 1);
v_val_3570_ = v_a_3598_;
goto v___jp_3569_;
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v_a_3599_ = lean_ctor_get(v___y_3597_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___y_3597_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___y_3597_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___y_3597_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
v___jp_3607_:
{
if (lean_obj_tag(v___y_3608_) == 0)
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___y_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___y_3608_, 1);
v_val_3570_ = v_a_3609_;
goto v___jp_3569_;
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref(v_type_3433_);
lean_dec(v_localInst2Index_3424_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
lean_dec_ref(v_xs_3417_);
v_a_3610_ = lean_ctor_get(v___y_3608_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___y_3608_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___y_3608_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___y_3608_);
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
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_inductiveTypeName_3415_ = stack[0].m_obj;
lean_object* v_us_3416_ = stack[1].m_obj;
lean_object* v_xs_3417_ = stack[2].m_obj;
lean_object* v___x_3418_ = stack[3].m_obj;
lean_object* v___x_3419_ = stack[4].m_obj;
lean_object* v_ctorName_3420_ = stack[5].m_obj;
lean_object* v___x_3421_ = stack[6].m_obj;
lean_object* v___f_3422_ = stack[7].m_obj;
lean_object* v_insts_3423_ = stack[8].m_obj;
lean_object* v_localInst2Index_3424_ = stack[9].m_obj;
lean_object* v___y_3425_ = stack[10].m_obj;
lean_object* v___y_3426_ = stack[11].m_obj;
lean_object* v___y_3427_ = stack[12].m_obj;
lean_object* v___y_3428_ = stack[13].m_obj;
lean_object* v___y_3429_ = stack[14].m_obj;
lean_object* v___y_3430_ = stack[15].m_obj;
lean_object* v_res_4019_;
v_res_4019_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_3415_, v_us_3416_, v_xs_3417_, v___x_3418_, v___x_3419_, v_ctorName_3420_, v___x_3421_, v___f_3422_, v_insts_3423_, v_localInst2Index_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
stack->m_obj
 = v_res_4019_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_4020_ = _args[0];
lean_object* v_us_4021_ = _args[1];
lean_object* v_xs_4022_ = _args[2];
lean_object* v___x_4023_ = _args[3];
lean_object* v___x_4024_ = _args[4];
lean_object* v_ctorName_4025_ = _args[5];
lean_object* v___x_4026_ = _args[6];
lean_object* v___f_4027_ = _args[7];
lean_object* v_insts_4028_ = _args[8];
lean_object* v_localInst2Index_4029_ = _args[9];
lean_object* v___y_4030_ = _args[10];
lean_object* v___y_4031_ = _args[11];
lean_object* v___y_4032_ = _args[12];
lean_object* v___y_4033_ = _args[13];
lean_object* v___y_4034_ = _args[14];
lean_object* v___y_4035_ = _args[15];
lean_object* v___y_4036_ = _args[16];
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_4020_, v_us_4021_, v_xs_4022_, v___x_4023_, v___x_4024_, v_ctorName_4025_, v___x_4026_, v___f_4027_, v_insts_4028_, v_localInst2Index_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec_ref(v_insts_4028_);
lean_dec_ref(v___x_4026_);
return v_res_4037_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_4038_, size_t v_i_4039_, lean_object* v_bs_4040_){
_start:
{
uint8_t v___x_4041_; 
v___x_4041_ = lean_usize_dec_lt(v_i_4039_, v_sz_4038_);
if (v___x_4041_ == 0)
{
return v_bs_4040_;
}
else
{
lean_object* v_v_4042_; lean_object* v___x_4043_; lean_object* v_bs_x27_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; size_t v___x_4049_; size_t v___x_4050_; lean_object* v___x_4051_; 
v_v_4042_ = lean_array_uget(v_bs_4040_, v_i_4039_);
v___x_4043_ = lean_unsigned_to_nat(0u);
v_bs_x27_4044_ = lean_array_uset(v_bs_4040_, v_i_4039_, v___x_4043_);
v___x_4045_ = l_Lean_Expr_fvarId_x21(v_v_4042_);
lean_dec(v_v_4042_);
v___x_4046_ = 1;
v___x_4047_ = lean_box(v___x_4046_);
v___x_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4045_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = ((size_t)1ULL);
v___x_4050_ = lean_usize_add(v_i_4039_, v___x_4049_);
v___x_4051_ = lean_array_uset(v_bs_x27_4044_, v_i_4039_, v___x_4048_);
v_i_4039_ = v___x_4050_;
v_bs_4040_ = v___x_4051_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4038_ = stack[0].m_num;
size_t v_i_4039_ = stack[1].m_num;
lean_object* v_bs_4040_ = stack[2].m_obj;
lean_object* v_res_4053_;
v_res_4053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4038_, v_i_4039_, v_bs_4040_);
stack->m_obj
 = v_res_4053_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_4054_, lean_object* v_i_4055_, lean_object* v_bs_4056_){
_start:
{
size_t v_sz_boxed_4057_; size_t v_i_boxed_4058_; lean_object* v_res_4059_; 
v_sz_boxed_4057_ = lean_unbox_usize(v_sz_4054_);
lean_dec(v_sz_4054_);
v_i_boxed_4058_ = lean_unbox_usize(v_i_4055_);
lean_dec(v_i_4055_);
v_res_4059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_4057_, v_i_boxed_4058_, v_bs_4056_);
return v_res_4059_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; 
lean_inc(v___y_4062_);
lean_inc_ref(v___y_4061_);
v___x_4068_ = lean_apply_7(v_k_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, lean_box(0));
return v___x_4068_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4060_ = stack[0].m_obj;
lean_object* v___y_4061_ = stack[1].m_obj;
lean_object* v___y_4062_ = stack[2].m_obj;
lean_object* v___y_4063_ = stack[3].m_obj;
lean_object* v___y_4064_ = stack[4].m_obj;
lean_object* v___y_4065_ = stack[5].m_obj;
lean_object* v___y_4066_ = stack[6].m_obj;
lean_object* v_res_4069_;
v_res_4069_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
stack->m_obj
 = v_res_4069_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4078_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_4079_, lean_object* v_k_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v___f_4088_; lean_object* v___x_4089_; 
lean_inc(v___y_4082_);
lean_inc_ref(v___y_4081_);
v___f_4088_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4088_, 0, v_k_4080_);
lean_closure_set(v___f_4088_, 1, v___y_4081_);
lean_closure_set(v___f_4088_, 2, v___y_4082_);
v___x_4089_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_4079_, v___f_4088_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4089_) == 0)
{
return v___x_4089_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
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
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_4079_ = stack[0].m_obj;
lean_object* v_k_4080_ = stack[1].m_obj;
lean_object* v___y_4081_ = stack[2].m_obj;
lean_object* v___y_4082_ = stack[3].m_obj;
lean_object* v___y_4083_ = stack[4].m_obj;
lean_object* v___y_4084_ = stack[5].m_obj;
lean_object* v___y_4085_ = stack[6].m_obj;
lean_object* v___y_4086_ = stack[7].m_obj;
lean_object* v_res_4098_;
v_res_4098_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4079_, v_k_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
stack->m_obj
 = v_res_4098_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4099_, lean_object* v_k_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4099_, v_k_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec_ref(v_bs_4099_);
return v_res_4108_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4109_, lean_object* v_k_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
size_t v_sz_4118_; size_t v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v_sz_4118_ = lean_array_size(v_bs_4109_);
v___x_4119_ = ((size_t)0ULL);
v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4118_, v___x_4119_, v_bs_4109_);
v___x_4121_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4120_, v_k_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec_ref(v___x_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_4109_ = stack[0].m_obj;
lean_object* v_k_4110_ = stack[1].m_obj;
lean_object* v___y_4111_ = stack[2].m_obj;
lean_object* v___y_4112_ = stack[3].m_obj;
lean_object* v___y_4113_ = stack[4].m_obj;
lean_object* v___y_4114_ = stack[5].m_obj;
lean_object* v___y_4115_ = stack[6].m_obj;
lean_object* v___y_4116_ = stack[7].m_obj;
lean_object* v_res_4122_;
v_res_4122_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4109_, v_k_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
stack->m_obj
 = v_res_4122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4123_, lean_object* v_k_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4123_, v_k_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4132_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4133_, lean_object* v_inductiveTypeName_4134_, lean_object* v_us_4135_, lean_object* v___x_4136_, lean_object* v_ctorName_4137_, lean_object* v___f_4138_, uint8_t v_addHypotheses_4139_, lean_object* v_xs_4140_, lean_object* v_x_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___f_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4149_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4140_, 2);
v___x_4150_ = l_Array_toSubarray___redArg(v_xs_4140_, v___x_4149_, v_numParams_4133_);
v___x_4151_ = l_Subarray_copy___redArg(v___x_4150_);
lean_inc_ref(v___x_4151_);
v___f_4152_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4152_, 0, v_inductiveTypeName_4134_);
lean_closure_set(v___f_4152_, 1, v_us_4135_);
lean_closure_set(v___f_4152_, 2, v_xs_4140_);
lean_closure_set(v___f_4152_, 3, v___x_4149_);
lean_closure_set(v___f_4152_, 4, v___x_4136_);
lean_closure_set(v___f_4152_, 5, v_ctorName_4137_);
lean_closure_set(v___f_4152_, 6, v___x_4151_);
lean_closure_set(v___f_4152_, 7, v___f_4138_);
v___x_4153_ = lean_box(v_addHypotheses_4139_);
v___x_4154_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4154_, 0, v___x_4153_);
lean_closure_set(v___x_4154_, 1, lean_box(0));
lean_closure_set(v___x_4154_, 2, v___x_4151_);
lean_closure_set(v___x_4154_, 3, v___f_4152_);
v___x_4155_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4140_, v___x_4154_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4155_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_4133_ = stack[0].m_obj;
lean_object* v_inductiveTypeName_4134_ = stack[1].m_obj;
lean_object* v_us_4135_ = stack[2].m_obj;
lean_object* v___x_4136_ = stack[3].m_obj;
lean_object* v_ctorName_4137_ = stack[4].m_obj;
lean_object* v___f_4138_ = stack[5].m_obj;
uint8_t v_addHypotheses_4139_ = stack[6].m_num;
lean_object* v_xs_4140_ = stack[7].m_obj;
lean_object* v_x_4141_ = stack[8].m_obj;
lean_object* v___y_4142_ = stack[9].m_obj;
lean_object* v___y_4143_ = stack[10].m_obj;
lean_object* v___y_4144_ = stack[11].m_obj;
lean_object* v___y_4145_ = stack[12].m_obj;
lean_object* v___y_4146_ = stack[13].m_obj;
lean_object* v___y_4147_ = stack[14].m_obj;
lean_object* v_res_4156_;
v_res_4156_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4133_, v_inductiveTypeName_4134_, v_us_4135_, v___x_4136_, v_ctorName_4137_, v___f_4138_, v_addHypotheses_4139_, v_xs_4140_, v_x_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
stack->m_obj
 = v_res_4156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4157_, lean_object* v_inductiveTypeName_4158_, lean_object* v_us_4159_, lean_object* v___x_4160_, lean_object* v_ctorName_4161_, lean_object* v___f_4162_, lean_object* v_addHypotheses_4163_, lean_object* v_xs_4164_, lean_object* v_x_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
uint8_t v_addHypotheses_boxed_4173_; lean_object* v_res_4174_; 
v_addHypotheses_boxed_4173_ = lean_unbox(v_addHypotheses_4163_);
v_res_4174_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4157_, v_inductiveTypeName_4158_, v_us_4159_, v___x_4160_, v_ctorName_4161_, v___f_4162_, v_addHypotheses_boxed_4173_, v_xs_4164_, v_x_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec_ref(v_x_4165_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
if (lean_obj_tag(v_a_4175_) == 0)
{
lean_object* v___x_4177_; 
v___x_4177_ = l_List_reverse___redArg(v_a_4176_);
return v___x_4177_;
}
else
{
lean_object* v_head_4178_; lean_object* v_tail_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4188_; 
v_head_4178_ = lean_ctor_get(v_a_4175_, 0);
v_tail_4179_ = lean_ctor_get(v_a_4175_, 1);
v_isSharedCheck_4188_ = !lean_is_exclusive(v_a_4175_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4181_ = v_a_4175_;
v_isShared_4182_ = v_isSharedCheck_4188_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_tail_4179_);
lean_inc(v_head_4178_);
lean_dec(v_a_4175_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4188_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4183_; lean_object* v___x_4185_; 
v___x_4183_ = l_Lean_Level_param___override(v_head_4178_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 1, v_a_4176_);
lean_ctor_set(v___x_4181_, 0, v___x_4183_);
v___x_4185_ = v___x_4181_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4183_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v_a_4176_);
v___x_4185_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
v_a_4175_ = v_tail_4179_;
v_a_4176_ = v___x_4185_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4190_, lean_object* v_ctorName_4191_, uint8_t v_addHypotheses_4192_, lean_object* v_indVal_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v_toConstantVal_4201_; lean_object* v_numParams_4202_; lean_object* v_levelParams_4203_; lean_object* v_type_4204_; lean_object* v___f_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v_us_4208_; lean_object* v___x_4209_; lean_object* v___f_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; 
v_toConstantVal_4201_ = lean_ctor_get(v_indVal_4193_, 0);
lean_inc_ref(v_toConstantVal_4201_);
v_numParams_4202_ = lean_ctor_get(v_indVal_4193_, 1);
lean_inc(v_numParams_4202_);
lean_dec_ref(v_indVal_4193_);
v_levelParams_4203_ = lean_ctor_get(v_toConstantVal_4201_, 1);
lean_inc(v_levelParams_4203_);
v_type_4204_ = lean_ctor_get(v_toConstantVal_4201_, 2);
lean_inc_ref(v_type_4204_);
lean_dec_ref(v_toConstantVal_4201_);
v___f_4205_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4206_ = lean_box(1);
v___x_4207_ = lean_box(0);
v_us_4208_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4203_, v___x_4207_);
v___x_4209_ = lean_box(v_addHypotheses_4192_);
v___f_4210_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4210_, 0, v_numParams_4202_);
lean_closure_set(v___f_4210_, 1, v_inductiveTypeName_4190_);
lean_closure_set(v___f_4210_, 2, v_us_4208_);
lean_closure_set(v___f_4210_, 3, v___x_4206_);
lean_closure_set(v___f_4210_, 4, v_ctorName_4191_);
lean_closure_set(v___f_4210_, 5, v___f_4205_);
lean_closure_set(v___f_4210_, 6, v___x_4209_);
v___x_4211_ = 0;
v___x_4212_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4204_, v___f_4210_, v___x_4211_, v___x_4211_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
return v___x_4212_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_inductiveTypeName_4190_ = stack[0].m_obj;
lean_object* v_ctorName_4191_ = stack[1].m_obj;
uint8_t v_addHypotheses_4192_ = stack[2].m_num;
lean_object* v_indVal_4193_ = stack[3].m_obj;
lean_object* v_a_4194_ = stack[4].m_obj;
lean_object* v_a_4195_ = stack[5].m_obj;
lean_object* v_a_4196_ = stack[6].m_obj;
lean_object* v_a_4197_ = stack[7].m_obj;
lean_object* v_a_4198_ = stack[8].m_obj;
lean_object* v_a_4199_ = stack[9].m_obj;
lean_object* v_res_4213_;
v_res_4213_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4190_, v_ctorName_4191_, v_addHypotheses_4192_, v_indVal_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
stack->m_obj
 = v_res_4213_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4214_, lean_object* v_ctorName_4215_, lean_object* v_addHypotheses_4216_, lean_object* v_indVal_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
uint8_t v_addHypotheses_boxed_4225_; lean_object* v_res_4226_; 
v_addHypotheses_boxed_4225_ = lean_unbox(v_addHypotheses_4216_);
v_res_4226_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4214_, v_ctorName_4215_, v_addHypotheses_boxed_4225_, v_indVal_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
lean_dec(v_a_4223_);
lean_dec_ref(v_a_4222_);
lean_dec(v_a_4221_);
lean_dec_ref(v_a_4220_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
return v_res_4226_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4227_, lean_object* v_bs_4228_, lean_object* v_k_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4228_, v_k_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
return v___x_4237_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_4228_ = stack[1].m_obj;
lean_object* v_k_4229_ = stack[2].m_obj;
lean_object* v___y_4230_ = stack[3].m_obj;
lean_object* v___y_4231_ = stack[4].m_obj;
lean_object* v___y_4232_ = stack[5].m_obj;
lean_object* v___y_4233_ = stack[6].m_obj;
lean_object* v___y_4234_ = stack[7].m_obj;
lean_object* v___y_4235_ = stack[8].m_obj;
lean_object* v_res_4238_;
v_res_4238_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_box(0), v_bs_4228_, v_k_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
stack->m_obj
 = v_res_4238_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4239_, lean_object* v_bs_4240_, lean_object* v_k_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4239_, v_bs_4240_, v_k_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec_ref(v_bs_4240_);
return v_res_4249_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4250_, lean_object* v_bs_4251_, lean_object* v_k_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4251_, v_k_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
return v___x_4260_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_4251_ = stack[1].m_obj;
lean_object* v_k_4252_ = stack[2].m_obj;
lean_object* v___y_4253_ = stack[3].m_obj;
lean_object* v___y_4254_ = stack[4].m_obj;
lean_object* v___y_4255_ = stack[5].m_obj;
lean_object* v___y_4256_ = stack[6].m_obj;
lean_object* v___y_4257_ = stack[7].m_obj;
lean_object* v___y_4258_ = stack[8].m_obj;
lean_object* v_res_4261_;
v_res_4261_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_box(0), v_bs_4251_, v_k_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
stack->m_obj
 = v_res_4261_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4262_, lean_object* v_bs_4263_, lean_object* v_k_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4262_, v_bs_4263_, v_k_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
return v_res_4272_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4273_, lean_object* v_levelParams_4274_, lean_object* v_type_4275_, lean_object* v_value_4276_, lean_object* v_hints_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v___x_4280_; uint8_t v___y_4282_; uint8_t v___y_4289_; lean_object* v_env_4292_; uint8_t v___x_4293_; 
v___x_4280_ = lean_st_ref_get(v___y_4278_);
v_env_4292_ = lean_ctor_get(v___x_4280_, 0);
lean_inc_ref_n(v_env_4292_, 2);
lean_dec(v___x_4280_);
v___x_4293_ = l_Lean_Environment_hasUnsafe(v_env_4292_, v_type_4275_);
if (v___x_4293_ == 0)
{
uint8_t v___x_4294_; 
v___x_4294_ = l_Lean_Environment_hasUnsafe(v_env_4292_, v_value_4276_);
v___y_4289_ = v___x_4294_;
goto v___jp_4288_;
}
else
{
lean_dec_ref(v_env_4292_);
v___y_4289_ = v___x_4293_;
goto v___jp_4288_;
}
v___jp_4281_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
lean_inc(v_name_4273_);
v___x_4283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4283_, 0, v_name_4273_);
lean_ctor_set(v___x_4283_, 1, v_levelParams_4274_);
lean_ctor_set(v___x_4283_, 2, v_type_4275_);
v___x_4284_ = lean_box(0);
v___x_4285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4285_, 0, v_name_4273_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4286_, 0, v___x_4283_);
lean_ctor_set(v___x_4286_, 1, v_value_4276_);
lean_ctor_set(v___x_4286_, 2, v_hints_4277_);
lean_ctor_set(v___x_4286_, 3, v___x_4285_);
lean_ctor_set_uint8(v___x_4286_, sizeof(void*)*4, v___y_4282_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
v___jp_4288_:
{
if (v___y_4289_ == 0)
{
uint8_t v___x_4290_; 
v___x_4290_ = 1;
v___y_4282_ = v___x_4290_;
goto v___jp_4281_;
}
else
{
uint8_t v___x_4291_; 
v___x_4291_ = 0;
v___y_4282_ = v___x_4291_;
goto v___jp_4281_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4273_ = stack[0].m_obj;
lean_object* v_levelParams_4274_ = stack[1].m_obj;
lean_object* v_type_4275_ = stack[2].m_obj;
lean_object* v_value_4276_ = stack[3].m_obj;
lean_object* v_hints_4277_ = stack[4].m_obj;
lean_object* v___y_4278_ = stack[5].m_obj;
lean_object* v_res_4295_;
v_res_4295_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4273_, v_levelParams_4274_, v_type_4275_, v_value_4276_, v_hints_4277_, v___y_4278_);
stack->m_obj
 = v_res_4295_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4296_, lean_object* v_levelParams_4297_, lean_object* v_type_4298_, lean_object* v_value_4299_, lean_object* v_hints_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4296_, v_levelParams_4297_, v_type_4298_, v_value_4299_, v_hints_4300_, v___y_4301_);
lean_dec(v___y_4301_);
return v_res_4303_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4304_, lean_object* v_levelParams_4305_, lean_object* v_type_4306_, lean_object* v_value_4307_, lean_object* v_hints_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4304_, v_levelParams_4305_, v_type_4306_, v_value_4307_, v_hints_4308_, v___y_4314_);
return v___x_4316_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4304_ = stack[0].m_obj;
lean_object* v_levelParams_4305_ = stack[1].m_obj;
lean_object* v_type_4306_ = stack[2].m_obj;
lean_object* v_value_4307_ = stack[3].m_obj;
lean_object* v_hints_4308_ = stack[4].m_obj;
lean_object* v___y_4309_ = stack[5].m_obj;
lean_object* v___y_4310_ = stack[6].m_obj;
lean_object* v___y_4311_ = stack[7].m_obj;
lean_object* v___y_4312_ = stack[8].m_obj;
lean_object* v___y_4313_ = stack[9].m_obj;
lean_object* v___y_4314_ = stack[10].m_obj;
lean_object* v_res_4317_;
v_res_4317_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4304_, v_levelParams_4305_, v_type_4306_, v_value_4307_, v_hints_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
stack->m_obj
 = v_res_4317_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4318_, lean_object* v_levelParams_4319_, lean_object* v_type_4320_, lean_object* v_value_4321_, lean_object* v_hints_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4318_, v_levelParams_4319_, v_type_4320_, v_value_4321_, v_hints_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
return v_res_4330_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4331_, uint8_t v_isExporting_4332_, lean_object* v___x_4333_, lean_object* v___y_4334_, lean_object* v___x_4335_, lean_object* v_a_x3f_4336_){
_start:
{
lean_object* v___x_4338_; lean_object* v_env_4339_; lean_object* v_nextMacroScope_4340_; lean_object* v_ngen_4341_; lean_object* v_auxDeclNGen_4342_; lean_object* v_traceState_4343_; lean_object* v_recordedDeps_4344_; lean_object* v_messages_4345_; lean_object* v_infoState_4346_; lean_object* v_snapshotTasks_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4372_; 
v___x_4338_ = lean_st_ref_take(v___y_4331_);
v_env_4339_ = lean_ctor_get(v___x_4338_, 0);
v_nextMacroScope_4340_ = lean_ctor_get(v___x_4338_, 1);
v_ngen_4341_ = lean_ctor_get(v___x_4338_, 2);
v_auxDeclNGen_4342_ = lean_ctor_get(v___x_4338_, 3);
v_traceState_4343_ = lean_ctor_get(v___x_4338_, 4);
v_recordedDeps_4344_ = lean_ctor_get(v___x_4338_, 6);
v_messages_4345_ = lean_ctor_get(v___x_4338_, 7);
v_infoState_4346_ = lean_ctor_get(v___x_4338_, 8);
v_snapshotTasks_4347_ = lean_ctor_get(v___x_4338_, 9);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4372_ == 0)
{
lean_object* v_unused_4373_; 
v_unused_4373_ = lean_ctor_get(v___x_4338_, 5);
lean_dec(v_unused_4373_);
v___x_4349_ = v___x_4338_;
v_isShared_4350_ = v_isSharedCheck_4372_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_snapshotTasks_4347_);
lean_inc(v_infoState_4346_);
lean_inc(v_messages_4345_);
lean_inc(v_recordedDeps_4344_);
lean_inc(v_traceState_4343_);
lean_inc(v_auxDeclNGen_4342_);
lean_inc(v_ngen_4341_);
lean_inc(v_nextMacroScope_4340_);
lean_inc(v_env_4339_);
lean_dec(v___x_4338_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4372_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4351_; lean_object* v___x_4353_; 
v___x_4351_ = l_Lean_Environment_setExporting(v_env_4339_, v_isExporting_4332_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 5, v___x_4333_);
lean_ctor_set(v___x_4349_, 0, v___x_4351_);
v___x_4353_ = v___x_4349_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4351_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_nextMacroScope_4340_);
lean_ctor_set(v_reuseFailAlloc_4371_, 2, v_ngen_4341_);
lean_ctor_set(v_reuseFailAlloc_4371_, 3, v_auxDeclNGen_4342_);
lean_ctor_set(v_reuseFailAlloc_4371_, 4, v_traceState_4343_);
lean_ctor_set(v_reuseFailAlloc_4371_, 5, v___x_4333_);
lean_ctor_set(v_reuseFailAlloc_4371_, 6, v_recordedDeps_4344_);
lean_ctor_set(v_reuseFailAlloc_4371_, 7, v_messages_4345_);
lean_ctor_set(v_reuseFailAlloc_4371_, 8, v_infoState_4346_);
lean_ctor_set(v_reuseFailAlloc_4371_, 9, v_snapshotTasks_4347_);
v___x_4353_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v_mctx_4356_; lean_object* v_zetaDeltaFVarIds_4357_; lean_object* v_postponed_4358_; lean_object* v_diag_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4369_; 
v___x_4354_ = lean_st_ref_put(v___y_4331_, v___x_4353_);
v___x_4355_ = lean_st_ref_take(v___y_4334_);
v_mctx_4356_ = lean_ctor_get(v___x_4355_, 0);
v_zetaDeltaFVarIds_4357_ = lean_ctor_get(v___x_4355_, 2);
v_postponed_4358_ = lean_ctor_get(v___x_4355_, 3);
v_diag_4359_ = lean_ctor_get(v___x_4355_, 4);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4369_ == 0)
{
lean_object* v_unused_4370_; 
v_unused_4370_ = lean_ctor_get(v___x_4355_, 1);
lean_dec(v_unused_4370_);
v___x_4361_ = v___x_4355_;
v_isShared_4362_ = v_isSharedCheck_4369_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_diag_4359_);
lean_inc(v_postponed_4358_);
lean_inc(v_zetaDeltaFVarIds_4357_);
lean_inc(v_mctx_4356_);
lean_dec(v___x_4355_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4369_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4363_; lean_object* v___x_4365_; 
v___x_4363_ = lean_box(0);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 1, v___x_4335_);
v___x_4365_ = v___x_4361_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_mctx_4356_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4368_, 2, v_zetaDeltaFVarIds_4357_);
lean_ctor_set(v_reuseFailAlloc_4368_, 3, v_postponed_4358_);
lean_ctor_set(v_reuseFailAlloc_4368_, 4, v_diag_4359_);
v___x_4365_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = lean_st_ref_put(v___y_4334_, v___x_4365_);
v___x_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4363_);
return v___x_4367_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4331_ = stack[0].m_obj;
uint8_t v_isExporting_4332_ = stack[1].m_num;
lean_object* v___x_4333_ = stack[2].m_obj;
lean_object* v___y_4334_ = stack[3].m_obj;
lean_object* v___x_4335_ = stack[4].m_obj;
lean_object* v_a_x3f_4336_ = stack[5].m_obj;
lean_object* v_res_4374_;
v_res_4374_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4331_, v_isExporting_4332_, v___x_4333_, v___y_4334_, v___x_4335_, v_a_x3f_4336_);
stack->m_obj
 = v_res_4374_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4375_, lean_object* v_isExporting_4376_, lean_object* v___x_4377_, lean_object* v___y_4378_, lean_object* v___x_4379_, lean_object* v_a_x3f_4380_, lean_object* v___y_4381_){
_start:
{
uint8_t v_isExporting_boxed_4382_; lean_object* v_res_4383_; 
v_isExporting_boxed_4382_ = lean_unbox(v_isExporting_4376_);
v_res_4383_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4375_, v_isExporting_boxed_4382_, v___x_4377_, v___y_4378_, v___x_4379_, v_a_x3f_4380_);
lean_dec(v_a_x3f_4380_);
lean_dec(v___y_4378_);
lean_dec(v___y_4375_);
return v_res_4383_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4384_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
return v___x_4388_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
lean_ctor_set(v___x_4390_, 2, v___x_4389_);
lean_ctor_set(v___x_4390_, 3, v___x_4389_);
lean_ctor_set(v___x_4390_, 4, v___x_4389_);
lean_ctor_set(v___x_4390_, 5, v___x_4389_);
return v___x_4390_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4391_, uint8_t v_isExporting_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; lean_object* v_env_4401_; lean_object* v___x_4402_; uint8_t v_isModule_4403_; 
v___x_4400_ = lean_st_ref_get(v___y_4398_);
v_env_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc_ref(v_env_4401_);
lean_dec(v___x_4400_);
v___x_4402_ = l_Lean_Environment_header(v_env_4401_);
v_isModule_4403_ = lean_ctor_get_uint8(v___x_4402_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4402_);
if (v_isModule_4403_ == 0)
{
lean_object* v___x_4404_; 
lean_dec_ref(v_env_4401_);
lean_inc(v___y_4398_);
lean_inc_ref(v___y_4397_);
lean_inc(v___y_4396_);
lean_inc_ref(v___y_4395_);
lean_inc(v___y_4394_);
lean_inc_ref(v___y_4393_);
v___x_4404_ = lean_apply_7(v_x_4391_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, lean_box(0));
return v___x_4404_;
}
else
{
uint8_t v_isExporting_4405_; 
v_isExporting_4405_ = lean_ctor_get_uint8(v_env_4401_, sizeof(void*)*13);
lean_dec_ref(v_env_4401_);
if (v_isExporting_4392_ == 0)
{
if (v_isExporting_4405_ == 0)
{
lean_object* v___x_4472_; 
lean_inc(v___y_4398_);
lean_inc_ref(v___y_4397_);
lean_inc(v___y_4396_);
lean_inc_ref(v___y_4395_);
lean_inc(v___y_4394_);
lean_inc_ref(v___y_4393_);
v___x_4472_ = lean_apply_7(v_x_4391_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, lean_box(0));
return v___x_4472_;
}
else
{
goto v___jp_4406_;
}
}
else
{
if (v_isExporting_4405_ == 0)
{
goto v___jp_4406_;
}
else
{
lean_object* v___x_4473_; 
lean_inc(v___y_4398_);
lean_inc_ref(v___y_4397_);
lean_inc(v___y_4396_);
lean_inc_ref(v___y_4395_);
lean_inc(v___y_4394_);
lean_inc_ref(v___y_4393_);
v___x_4473_ = lean_apply_7(v_x_4391_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, lean_box(0));
return v___x_4473_;
}
}
v___jp_4406_:
{
lean_object* v___x_4407_; lean_object* v_env_4408_; lean_object* v_nextMacroScope_4409_; lean_object* v_ngen_4410_; lean_object* v_auxDeclNGen_4411_; lean_object* v_traceState_4412_; lean_object* v_recordedDeps_4413_; lean_object* v_messages_4414_; lean_object* v_infoState_4415_; lean_object* v_snapshotTasks_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4470_; 
v___x_4407_ = lean_st_ref_take(v___y_4398_);
v_env_4408_ = lean_ctor_get(v___x_4407_, 0);
v_nextMacroScope_4409_ = lean_ctor_get(v___x_4407_, 1);
v_ngen_4410_ = lean_ctor_get(v___x_4407_, 2);
v_auxDeclNGen_4411_ = lean_ctor_get(v___x_4407_, 3);
v_traceState_4412_ = lean_ctor_get(v___x_4407_, 4);
v_recordedDeps_4413_ = lean_ctor_get(v___x_4407_, 6);
v_messages_4414_ = lean_ctor_get(v___x_4407_, 7);
v_infoState_4415_ = lean_ctor_get(v___x_4407_, 8);
v_snapshotTasks_4416_ = lean_ctor_get(v___x_4407_, 9);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4470_ == 0)
{
lean_object* v_unused_4471_; 
v_unused_4471_ = lean_ctor_get(v___x_4407_, 5);
lean_dec(v_unused_4471_);
v___x_4418_ = v___x_4407_;
v_isShared_4419_ = v_isSharedCheck_4470_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_snapshotTasks_4416_);
lean_inc(v_infoState_4415_);
lean_inc(v_messages_4414_);
lean_inc(v_recordedDeps_4413_);
lean_inc(v_traceState_4412_);
lean_inc(v_auxDeclNGen_4411_);
lean_inc(v_ngen_4410_);
lean_inc(v_nextMacroScope_4409_);
lean_inc(v_env_4408_);
lean_dec(v___x_4407_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4470_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4420_ = l_Lean_Environment_setExporting(v_env_4408_, v_isExporting_4392_);
v___x_4421_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 5, v___x_4421_);
lean_ctor_set(v___x_4418_, 0, v___x_4420_);
v___x_4423_ = v___x_4418_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4420_);
lean_ctor_set(v_reuseFailAlloc_4469_, 1, v_nextMacroScope_4409_);
lean_ctor_set(v_reuseFailAlloc_4469_, 2, v_ngen_4410_);
lean_ctor_set(v_reuseFailAlloc_4469_, 3, v_auxDeclNGen_4411_);
lean_ctor_set(v_reuseFailAlloc_4469_, 4, v_traceState_4412_);
lean_ctor_set(v_reuseFailAlloc_4469_, 5, v___x_4421_);
lean_ctor_set(v_reuseFailAlloc_4469_, 6, v_recordedDeps_4413_);
lean_ctor_set(v_reuseFailAlloc_4469_, 7, v_messages_4414_);
lean_ctor_set(v_reuseFailAlloc_4469_, 8, v_infoState_4415_);
lean_ctor_set(v_reuseFailAlloc_4469_, 9, v_snapshotTasks_4416_);
v___x_4423_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v_mctx_4426_; lean_object* v_zetaDeltaFVarIds_4427_; lean_object* v_postponed_4428_; lean_object* v_diag_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4467_; 
v___x_4424_ = lean_st_ref_put(v___y_4398_, v___x_4423_);
v___x_4425_ = lean_st_ref_take(v___y_4396_);
v_mctx_4426_ = lean_ctor_get(v___x_4425_, 0);
v_zetaDeltaFVarIds_4427_ = lean_ctor_get(v___x_4425_, 2);
v_postponed_4428_ = lean_ctor_get(v___x_4425_, 3);
v_diag_4429_ = lean_ctor_get(v___x_4425_, 4);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4467_ == 0)
{
lean_object* v_unused_4468_; 
v_unused_4468_ = lean_ctor_get(v___x_4425_, 1);
lean_dec(v_unused_4468_);
v___x_4431_ = v___x_4425_;
v_isShared_4432_ = v_isSharedCheck_4467_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_diag_4429_);
lean_inc(v_postponed_4428_);
lean_inc(v_zetaDeltaFVarIds_4427_);
lean_inc(v_mctx_4426_);
lean_dec(v___x_4425_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4467_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4433_; lean_object* v___x_4435_; 
v___x_4433_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 1, v___x_4433_);
v___x_4435_ = v___x_4431_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_mctx_4426_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4466_, 2, v_zetaDeltaFVarIds_4427_);
lean_ctor_set(v_reuseFailAlloc_4466_, 3, v_postponed_4428_);
lean_ctor_set(v_reuseFailAlloc_4466_, 4, v_diag_4429_);
v___x_4435_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4436_; lean_object* v_r_4437_; 
v___x_4436_ = lean_st_ref_put(v___y_4396_, v___x_4435_);
lean_inc(v___y_4398_);
lean_inc_ref(v___y_4397_);
lean_inc(v___y_4396_);
lean_inc_ref(v___y_4395_);
lean_inc(v___y_4394_);
lean_inc_ref(v___y_4393_);
v_r_4437_ = lean_apply_7(v_x_4391_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, lean_box(0));
if (lean_obj_tag(v_r_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4454_; 
v_a_4438_ = lean_ctor_get(v_r_4437_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_r_4437_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4440_ = v_r_4437_;
v_isShared_4441_ = v_isSharedCheck_4454_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v_r_4437_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4454_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
lean_inc(v_a_4438_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set_tag(v___x_4440_, 1);
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
lean_object* v___x_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
v___x_4444_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4398_, v_isExporting_4405_, v___x_4421_, v___y_4396_, v___x_4433_, v___x_4443_);
lean_dec_ref(v___x_4443_);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4451_ == 0)
{
lean_object* v_unused_4452_; 
v_unused_4452_ = lean_ctor_get(v___x_4444_, 0);
lean_dec(v_unused_4452_);
v___x_4446_ = v___x_4444_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_dec(v___x_4444_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 0, v_a_4438_);
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4438_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
v_a_4455_ = lean_ctor_get(v_r_4437_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v_r_4437_, 1);
v___x_4456_ = lean_box(0);
v___x_4457_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4398_, v_isExporting_4405_, v___x_4421_, v___y_4396_, v___x_4433_, v___x_4456_);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4464_ == 0)
{
lean_object* v_unused_4465_; 
v_unused_4465_ = lean_ctor_get(v___x_4457_, 0);
lean_dec(v_unused_4465_);
v___x_4459_ = v___x_4457_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_dec(v___x_4457_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set_tag(v___x_4459_, 1);
lean_ctor_set(v___x_4459_, 0, v_a_4455_);
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4455_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4391_ = stack[0].m_obj;
uint8_t v_isExporting_4392_ = stack[1].m_num;
lean_object* v___y_4393_ = stack[2].m_obj;
lean_object* v___y_4394_ = stack[3].m_obj;
lean_object* v___y_4395_ = stack[4].m_obj;
lean_object* v___y_4396_ = stack[5].m_obj;
lean_object* v___y_4397_ = stack[6].m_obj;
lean_object* v___y_4398_ = stack[7].m_obj;
lean_object* v_res_4474_;
v_res_4474_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4391_, v_isExporting_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
stack->m_obj
 = v_res_4474_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4475_, lean_object* v_isExporting_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
uint8_t v_isExporting_boxed_4484_; lean_object* v_res_4485_; 
v_isExporting_boxed_4484_ = lean_unbox(v_isExporting_4476_);
v_res_4485_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4475_, v_isExporting_boxed_4484_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
return v_res_4485_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4486_, lean_object* v_x_4487_, uint8_t v_isExporting_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4487_, v_isExporting_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4496_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4487_ = stack[1].m_obj;
uint8_t v_isExporting_4488_ = stack[2].m_num;
lean_object* v___y_4489_ = stack[3].m_obj;
lean_object* v___y_4490_ = stack[4].m_obj;
lean_object* v___y_4491_ = stack[5].m_obj;
lean_object* v___y_4492_ = stack[6].m_obj;
lean_object* v___y_4493_ = stack[7].m_obj;
lean_object* v___y_4494_ = stack[8].m_obj;
lean_object* v_res_4497_;
v_res_4497_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_box(0), v_x_4487_, v_isExporting_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
stack->m_obj
 = v_res_4497_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4498_, lean_object* v_x_4499_, lean_object* v_isExporting_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
uint8_t v_isExporting_boxed_4508_; lean_object* v_res_4509_; 
v_isExporting_boxed_4508_ = lean_unbox(v_isExporting_4500_);
v_res_4509_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4498_, v_x_4499_, v_isExporting_boxed_4508_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
return v_res_4509_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_4512_ = stack[0].m_obj;
lean_object* v___y_4513_ = stack[1].m_obj;
lean_object* v___y_4514_ = stack[2].m_obj;
lean_object* v___y_4515_ = stack[3].m_obj;
lean_object* v___y_4516_ = stack[4].m_obj;
lean_object* v___y_4517_ = stack[5].m_obj;
lean_object* v___y_4518_ = stack[6].m_obj;
lean_object* v_res_4522_;
v_res_4522_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
stack->m_obj
 = v_res_4522_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
return v_res_4531_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4534_ = l_Lean_stringToMessageData(v___x_4533_);
return v___x_4534_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4537_ = l_Lean_stringToMessageData(v___x_4536_);
return v___x_4537_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4540_ = l_Lean_stringToMessageData(v___x_4539_);
return v___x_4540_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4541_, lean_object* v___x_4542_, lean_object* v_inductiveTypeName_4543_, uint8_t v___x_4544_, lean_object* v___x_4545_, lean_object* v___f_4546_, lean_object* v_ctorName_4547_, uint8_t v_addHypotheses_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v___y_4557_; lean_object* v___x_4560_; 
lean_inc(v_inductiveTypeName_4543_);
v___x_4560_ = l_Lean_Elab_Deriving_mkContext(v___x_4541_, v___x_4542_, v_inductiveTypeName_4543_, v___x_4544_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_toCold_4561_; lean_object* v_a_4562_; lean_object* v_options_4563_; lean_object* v_currNamespace_4564_; lean_object* v_inheritedTraceOptions_4565_; lean_object* v_instName_4566_; lean_object* v_auxFunNames_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; uint8_t v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; uint8_t v___y_4622_; lean_object* v___y_4661_; uint8_t v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___x_4676_; 
v_toCold_4561_ = lean_ctor_get(v___y_4553_, 0);
v_a_4562_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4562_);
lean_dec_ref_known(v___x_4560_, 1);
v_options_4563_ = lean_ctor_get(v_toCold_4561_, 2);
v_currNamespace_4564_ = lean_ctor_get(v_toCold_4561_, 4);
v_inheritedTraceOptions_4565_ = lean_ctor_get(v_toCold_4561_, 11);
v_instName_4566_ = lean_ctor_get(v_a_4562_, 0);
lean_inc(v_instName_4566_);
v_auxFunNames_4567_ = lean_ctor_get(v_a_4562_, 2);
lean_inc_ref(v_auxFunNames_4567_);
lean_dec(v_a_4562_);
v___x_4568_ = lean_unsigned_to_nat(0u);
v___x_4569_ = lean_array_get(v___x_4545_, v_auxFunNames_4567_, v___x_4568_);
lean_dec_ref(v_auxFunNames_4567_);
lean_inc(v_currNamespace_4564_);
v___x_4570_ = l_Lean_Name_append(v_currNamespace_4564_, v___x_4569_);
lean_inc(v_inductiveTypeName_4543_);
v___x_4676_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4543_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v_a_4679_; lean_object* v___y_4751_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc_n(v_a_4677_, 2);
lean_dec_ref_known(v___x_4676_, 1);
v___x_4773_ = lean_box(v_addHypotheses_4548_);
lean_inc(v_inductiveTypeName_4543_);
v___x_4774_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4774_, 0, v_inductiveTypeName_4543_);
lean_closure_set(v___x_4774_, 1, v_ctorName_4547_);
lean_closure_set(v___x_4774_, 2, v___x_4773_);
lean_closure_set(v___x_4774_, 3, v_a_4677_);
lean_inc(v___x_4570_);
v___x_4775_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4570_, v___x_4774_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; 
lean_dec_ref(v___f_4546_);
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref_known(v___x_4775_, 1);
v_a_4679_ = v_a_4776_;
goto v___jp_4678_;
}
else
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4806_; 
v_a_4777_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4779_ = v___x_4775_;
v_isShared_4780_ = v_isSharedCheck_4806_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4775_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4806_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
uint8_t v___y_4782_; uint8_t v___x_4804_; 
v___x_4804_ = l_Lean_Exception_isInterrupt(v_a_4777_);
if (v___x_4804_ == 0)
{
uint8_t v___x_4805_; 
lean_inc(v_a_4777_);
v___x_4805_ = l_Lean_Exception_isRuntime(v_a_4777_);
v___y_4782_ = v___x_4805_;
goto v___jp_4781_;
}
else
{
v___y_4782_ = v___x_4804_;
goto v___jp_4781_;
}
v___jp_4781_:
{
if (v___y_4782_ == 0)
{
uint8_t v_hasTrace_4783_; 
lean_del_object(v___x_4779_);
v_hasTrace_4783_ = lean_ctor_get_uint8(v_options_4563_, sizeof(void*)*1);
if (v_hasTrace_4783_ == 0)
{
lean_dec(v_a_4777_);
goto v___jp_4770_;
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4784_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4785_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4565_, v_options_4563_, v___x_4785_);
if (v___x_4786_ == 0)
{
lean_dec(v_a_4777_);
goto v___jp_4770_;
}
else
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4787_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4788_ = l_Lean_Exception_toMessageData(v_a_4777_);
v___x_4789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4787_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4784_, v___x_4789_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4792_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc(v_a_4791_);
lean_dec_ref_known(v___x_4790_, 1);
lean_inc(v___y_4554_);
lean_inc_ref(v___y_4553_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
v___x_4792_ = lean_apply_8(v___f_4546_, v_a_4791_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, lean_box(0));
v___y_4751_ = v___x_4792_;
goto v___jp_4750_;
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v_a_4677_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec_ref(v___f_4546_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4793_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4790_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4790_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
}
else
{
lean_object* v___x_4802_; 
lean_dec(v_a_4677_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec_ref(v___f_4546_);
lean_dec(v_inductiveTypeName_4543_);
if (v_isShared_4780_ == 0)
{
v___x_4802_ = v___x_4779_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4777_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
v___jp_4678_:
{
lean_object* v_snd_4680_; lean_object* v_fst_4681_; lean_object* v_fst_4682_; lean_object* v_snd_4683_; lean_object* v___x_4684_; lean_object* v_toConstantVal_4685_; lean_object* v_env_4686_; lean_object* v_levelParams_4687_; uint32_t v___x_4688_; uint32_t v___x_4689_; uint32_t v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4749_; 
v_snd_4680_ = lean_ctor_get(v_a_4679_, 1);
lean_inc(v_snd_4680_);
v_fst_4681_ = lean_ctor_get(v_a_4679_, 0);
lean_inc(v_fst_4681_);
lean_dec_ref(v_a_4679_);
v_fst_4682_ = lean_ctor_get(v_snd_4680_, 0);
lean_inc_n(v_fst_4682_, 2);
v_snd_4683_ = lean_ctor_get(v_snd_4680_, 1);
lean_inc(v_snd_4683_);
lean_dec(v_snd_4680_);
v___x_4684_ = lean_st_ref_get(v___y_4554_);
v_toConstantVal_4685_ = lean_ctor_get(v_a_4677_, 0);
lean_inc_ref(v_toConstantVal_4685_);
lean_dec(v_a_4677_);
v_env_4686_ = lean_ctor_get(v___x_4684_, 0);
lean_inc_ref(v_env_4686_);
lean_dec(v___x_4684_);
v_levelParams_4687_ = lean_ctor_get(v_toConstantVal_4685_, 1);
lean_inc(v_levelParams_4687_);
lean_dec_ref(v_toConstantVal_4685_);
v___x_4688_ = l_Lean_getMaxHeight(v_env_4686_, v_fst_4682_);
v___x_4689_ = 1;
v___x_4690_ = lean_uint32_add(v___x_4688_, v___x_4689_);
v___x_4691_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4691_, 0, v___x_4690_);
lean_inc(v___x_4570_);
v___x_4692_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4570_, v_levelParams_4687_, v_fst_4681_, v_fst_4682_, v___x_4691_, v___y_4554_);
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4749_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4749_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
lean_ctor_set_tag(v___x_4695_, 1);
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
uint8_t v___x_4699_; lean_object* v___x_4700_; 
v___x_4699_ = 0;
v___x_4700_ = l_Lean_addDecl(v___x_4698_, v___x_4699_, v___y_4553_, v___y_4554_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v___x_4701_; lean_object* v_env_4702_; uint8_t v___x_4703_; 
lean_dec_ref_known(v___x_4700_, 1);
v___x_4701_ = lean_st_ref_get(v___y_4554_);
v_env_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc_ref(v_env_4702_);
lean_dec(v___x_4701_);
lean_inc(v_inductiveTypeName_4543_);
v___x_4703_ = l_Lean_isMarkedMeta(v_env_4702_, v_inductiveTypeName_4543_);
if (v___x_4703_ == 0)
{
v___y_4661_ = v_snd_4683_;
v___y_4662_ = v___x_4699_;
v___y_4663_ = v___y_4549_;
v___y_4664_ = v___y_4550_;
v___y_4665_ = v___y_4551_;
v___y_4666_ = v___y_4552_;
v___y_4667_ = v___y_4553_;
v___y_4668_ = v___y_4554_;
goto v___jp_4660_;
}
else
{
lean_object* v___x_4704_; lean_object* v_env_4705_; lean_object* v_nextMacroScope_4706_; lean_object* v_ngen_4707_; lean_object* v_auxDeclNGen_4708_; lean_object* v_traceState_4709_; lean_object* v_recordedDeps_4710_; lean_object* v_messages_4711_; lean_object* v_infoState_4712_; lean_object* v_snapshotTasks_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4738_; 
v___x_4704_ = lean_st_ref_take(v___y_4554_);
v_env_4705_ = lean_ctor_get(v___x_4704_, 0);
v_nextMacroScope_4706_ = lean_ctor_get(v___x_4704_, 1);
v_ngen_4707_ = lean_ctor_get(v___x_4704_, 2);
v_auxDeclNGen_4708_ = lean_ctor_get(v___x_4704_, 3);
v_traceState_4709_ = lean_ctor_get(v___x_4704_, 4);
v_recordedDeps_4710_ = lean_ctor_get(v___x_4704_, 6);
v_messages_4711_ = lean_ctor_get(v___x_4704_, 7);
v_infoState_4712_ = lean_ctor_get(v___x_4704_, 8);
v_snapshotTasks_4713_ = lean_ctor_get(v___x_4704_, 9);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4738_ == 0)
{
lean_object* v_unused_4739_; 
v_unused_4739_ = lean_ctor_get(v___x_4704_, 5);
lean_dec(v_unused_4739_);
v___x_4715_ = v___x_4704_;
v_isShared_4716_ = v_isSharedCheck_4738_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_snapshotTasks_4713_);
lean_inc(v_infoState_4712_);
lean_inc(v_messages_4711_);
lean_inc(v_recordedDeps_4710_);
lean_inc(v_traceState_4709_);
lean_inc(v_auxDeclNGen_4708_);
lean_inc(v_ngen_4707_);
lean_inc(v_nextMacroScope_4706_);
lean_inc(v_env_4705_);
lean_dec(v___x_4704_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4738_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4720_; 
lean_inc(v___x_4570_);
v___x_4717_ = l_Lean_markMeta(v_env_4705_, v___x_4570_);
v___x_4718_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 5, v___x_4718_);
lean_ctor_set(v___x_4715_, 0, v___x_4717_);
v___x_4720_ = v___x_4715_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_nextMacroScope_4706_);
lean_ctor_set(v_reuseFailAlloc_4737_, 2, v_ngen_4707_);
lean_ctor_set(v_reuseFailAlloc_4737_, 3, v_auxDeclNGen_4708_);
lean_ctor_set(v_reuseFailAlloc_4737_, 4, v_traceState_4709_);
lean_ctor_set(v_reuseFailAlloc_4737_, 5, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4737_, 6, v_recordedDeps_4710_);
lean_ctor_set(v_reuseFailAlloc_4737_, 7, v_messages_4711_);
lean_ctor_set(v_reuseFailAlloc_4737_, 8, v_infoState_4712_);
lean_ctor_set(v_reuseFailAlloc_4737_, 9, v_snapshotTasks_4713_);
v___x_4720_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v_mctx_4723_; lean_object* v_zetaDeltaFVarIds_4724_; lean_object* v_postponed_4725_; lean_object* v_diag_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4735_; 
v___x_4721_ = lean_st_ref_put(v___y_4554_, v___x_4720_);
v___x_4722_ = lean_st_ref_take(v___y_4552_);
v_mctx_4723_ = lean_ctor_get(v___x_4722_, 0);
v_zetaDeltaFVarIds_4724_ = lean_ctor_get(v___x_4722_, 2);
v_postponed_4725_ = lean_ctor_get(v___x_4722_, 3);
v_diag_4726_ = lean_ctor_get(v___x_4722_, 4);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4735_ == 0)
{
lean_object* v_unused_4736_; 
v_unused_4736_ = lean_ctor_get(v___x_4722_, 1);
lean_dec(v_unused_4736_);
v___x_4728_ = v___x_4722_;
v_isShared_4729_ = v_isSharedCheck_4735_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_diag_4726_);
lean_inc(v_postponed_4725_);
lean_inc(v_zetaDeltaFVarIds_4724_);
lean_inc(v_mctx_4723_);
lean_dec(v___x_4722_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4735_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4730_; lean_object* v___x_4732_; 
v___x_4730_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 1, v___x_4730_);
v___x_4732_ = v___x_4728_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_mctx_4723_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4734_, 2, v_zetaDeltaFVarIds_4724_);
lean_ctor_set(v_reuseFailAlloc_4734_, 3, v_postponed_4725_);
lean_ctor_set(v_reuseFailAlloc_4734_, 4, v_diag_4726_);
v___x_4732_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4733_; 
v___x_4733_ = lean_st_ref_put(v___y_4552_, v___x_4732_);
v___y_4661_ = v_snd_4683_;
v___y_4662_ = v___x_4699_;
v___y_4663_ = v___y_4549_;
v___y_4664_ = v___y_4550_;
v___y_4665_ = v___y_4551_;
v___y_4666_ = v___y_4552_;
v___y_4667_ = v___y_4553_;
v___y_4668_ = v___y_4554_;
goto v___jp_4660_;
}
}
}
}
}
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
lean_dec(v_snd_4683_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4740_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4742_ = v___x_4700_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4700_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
}
}
v___jp_4750_:
{
if (lean_obj_tag(v___y_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4761_; 
v_a_4752_ = lean_ctor_get(v___y_4751_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___y_4751_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4754_ = v___y_4751_;
v_isShared_4755_ = v_isSharedCheck_4761_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___y_4751_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4761_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
if (lean_obj_tag(v_a_4752_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; 
lean_dec(v_a_4677_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4756_ = lean_ctor_get(v_a_4752_, 0);
lean_inc(v_a_4756_);
lean_dec_ref_known(v_a_4752_, 1);
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 0, v_a_4756_);
v___x_4758_ = v___x_4754_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4756_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
else
{
lean_object* v_a_4760_; 
lean_del_object(v___x_4754_);
v_a_4760_ = lean_ctor_get(v_a_4752_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v_a_4752_, 1);
v_a_4679_ = v_a_4760_;
goto v___jp_4678_;
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_dec(v_a_4677_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4762_ = lean_ctor_get(v___y_4751_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___y_4751_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___y_4751_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___y_4751_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
v___jp_4770_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4771_ = lean_box(0);
lean_inc(v___y_4554_);
lean_inc_ref(v___y_4553_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
v___x_4772_ = lean_apply_8(v___f_4546_, v___x_4771_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, lean_box(0));
v___y_4751_ = v___x_4772_;
goto v___jp_4750_;
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v_ctorName_4547_);
lean_dec_ref(v___f_4546_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4807_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4676_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4676_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
v___jp_4571_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4580_ = l_Lean_mkIdent(v_instName_4566_);
v___x_4581_ = l_Lean_mkCIdent(v___x_4570_);
v___x_4582_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4543_, v___x_4580_, v___y_4572_, v___x_4581_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4572_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_toCold_4583_; lean_object* v_options_4584_; uint8_t v_hasTrace_4585_; 
v_toCold_4583_ = lean_ctor_get(v___y_4578_, 0);
v_options_4584_ = lean_ctor_get(v_toCold_4583_, 2);
v_hasTrace_4585_ = lean_ctor_get_uint8(v_options_4584_, sizeof(void*)*1);
if (v_hasTrace_4585_ == 0)
{
lean_object* v_a_4586_; 
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4573_);
v_a_4586_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v___x_4582_, 1);
v___y_4557_ = v_a_4586_;
goto v___jp_4556_;
}
else
{
lean_object* v_a_4587_; lean_object* v_inheritedTraceOptions_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; uint8_t v___x_4591_; 
v_a_4587_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4582_, 1);
v_inheritedTraceOptions_4588_ = lean_ctor_get(v_toCold_4583_, 11);
v___x_4589_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4573_);
v___x_4590_ = l_Lean_Name_append(v___x_4589_, v___y_4573_);
v___x_4591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4588_, v_options_4584_, v___x_4590_);
lean_dec(v___x_4590_);
if (v___x_4591_ == 0)
{
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4573_);
v___y_4557_ = v_a_4587_;
goto v___jp_4556_;
}
else
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4592_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4587_);
v___x_4593_ = l_Lean_MessageData_ofSyntax(v_a_4587_);
v___x_4594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4592_);
lean_ctor_set(v___x_4594_, 1, v___x_4593_);
v___x_4595_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4573_, v___x_4594_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_dec_ref_known(v___x_4595_, 1);
v___y_4557_ = v_a_4587_;
goto v___jp_4556_;
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_dec(v_a_4587_);
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4573_);
v_a_4604_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4582_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4582_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
v___jp_4612_:
{
lean_object* v___x_4623_; 
v___x_4623_ = l_Lean_compileDecls(v___y_4613_, v___y_4622_, v___y_4616_, v___y_4615_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v___x_4624_; 
lean_dec_ref_known(v___x_4623_, 1);
lean_inc(v___x_4570_);
v___x_4624_ = l_Lean_enableRealizationsForConst(v___x_4570_, v___y_4616_, v___y_4615_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_toCold_4625_; lean_object* v_options_4626_; lean_object* v_inheritedTraceOptions_4627_; uint8_t v_hasTrace_4628_; lean_object* v___x_4629_; 
lean_dec_ref_known(v___x_4624_, 1);
v_toCold_4625_ = lean_ctor_get(v___y_4616_, 0);
v_options_4626_ = lean_ctor_get(v_toCold_4625_, 2);
v_inheritedTraceOptions_4627_ = lean_ctor_get(v_toCold_4625_, 11);
v_hasTrace_4628_ = lean_ctor_get_uint8(v_options_4626_, sizeof(void*)*1);
v___x_4629_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4628_ == 0)
{
v___y_4572_ = v___y_4614_;
v___y_4573_ = v___x_4629_;
v___y_4574_ = v___y_4621_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4617_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4616_;
v___y_4579_ = v___y_4615_;
goto v___jp_4571_;
}
else
{
lean_object* v___x_4630_; uint8_t v___x_4631_; 
v___x_4630_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4627_, v_options_4626_, v___x_4630_);
if (v___x_4631_ == 0)
{
v___y_4572_ = v___y_4614_;
v___y_4573_ = v___x_4629_;
v___y_4574_ = v___y_4621_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4617_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4616_;
v___y_4579_ = v___y_4615_;
goto v___jp_4571_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4632_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4570_);
v___x_4633_ = l_Lean_MessageData_ofConstName(v___x_4570_, v___y_4619_);
v___x_4634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4632_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
v___x_4635_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4629_, v___x_4634_, v___y_4617_, v___y_4620_, v___y_4616_, v___y_4615_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_dec_ref_known(v___x_4635_, 1);
v___y_4572_ = v___y_4614_;
v___y_4573_ = v___x_4629_;
v___y_4574_ = v___y_4621_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4617_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4616_;
v___y_4579_ = v___y_4615_;
goto v___jp_4571_;
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4635_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4635_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4644_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4624_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4624_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec(v___x_4570_);
lean_dec(v_instName_4566_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4652_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4623_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4623_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
v___jp_4660_:
{
lean_object* v___x_4669_; lean_object* v_env_4670_; uint8_t v_isNoncomputableSection_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4669_ = lean_st_ref_get(v___y_4668_);
v_env_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc_ref(v_env_4670_);
lean_dec(v___x_4669_);
v_isNoncomputableSection_4671_ = lean_ctor_get_uint8(v___y_4663_, sizeof(void*)*8 + 4);
v___x_4672_ = lean_unsigned_to_nat(1u);
v___x_4673_ = lean_mk_empty_array_with_capacity(v___x_4672_);
lean_inc(v___x_4570_);
v___x_4674_ = lean_array_push(v___x_4673_, v___x_4570_);
if (v_isNoncomputableSection_4671_ == 0)
{
lean_dec_ref(v_env_4670_);
v___y_4613_ = v___x_4674_;
v___y_4614_ = v___y_4661_;
v___y_4615_ = v___y_4668_;
v___y_4616_ = v___y_4667_;
v___y_4617_ = v___y_4665_;
v___y_4618_ = v___y_4664_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4666_;
v___y_4621_ = v___y_4663_;
v___y_4622_ = v___x_4544_;
goto v___jp_4612_;
}
else
{
uint8_t v___x_4675_; 
lean_inc(v___x_4570_);
v___x_4675_ = l_Lean_isMarkedMeta(v_env_4670_, v___x_4570_);
v___y_4613_ = v___x_4674_;
v___y_4614_ = v___y_4661_;
v___y_4615_ = v___y_4668_;
v___y_4616_ = v___y_4667_;
v___y_4617_ = v___y_4665_;
v___y_4618_ = v___y_4664_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4666_;
v___y_4621_ = v___y_4663_;
v___y_4622_ = v___x_4675_;
goto v___jp_4612_;
}
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v_ctorName_4547_);
lean_dec_ref(v___f_4546_);
lean_dec(v_inductiveTypeName_4543_);
v_a_4815_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4560_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4560_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
v___jp_4556_:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___y_4557_);
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
return v___x_4559_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4541_ = stack[0].m_obj;
lean_object* v___x_4542_ = stack[1].m_obj;
lean_object* v_inductiveTypeName_4543_ = stack[2].m_obj;
uint8_t v___x_4544_ = stack[3].m_num;
lean_object* v___x_4545_ = stack[4].m_obj;
lean_object* v___f_4546_ = stack[5].m_obj;
lean_object* v_ctorName_4547_ = stack[6].m_obj;
uint8_t v_addHypotheses_4548_ = stack[7].m_num;
lean_object* v___y_4549_ = stack[8].m_obj;
lean_object* v___y_4550_ = stack[9].m_obj;
lean_object* v___y_4551_ = stack[10].m_obj;
lean_object* v___y_4552_ = stack[11].m_obj;
lean_object* v___y_4553_ = stack[12].m_obj;
lean_object* v___y_4554_ = stack[13].m_obj;
lean_object* v_res_4823_;
v_res_4823_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4541_, v___x_4542_, v_inductiveTypeName_4543_, v___x_4544_, v___x_4545_, v___f_4546_, v_ctorName_4547_, v_addHypotheses_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
stack->m_obj
 = v_res_4823_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4824_, lean_object* v___x_4825_, lean_object* v_inductiveTypeName_4826_, lean_object* v___x_4827_, lean_object* v___x_4828_, lean_object* v___f_4829_, lean_object* v_ctorName_4830_, lean_object* v_addHypotheses_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
uint8_t v___x_16900__boxed_4839_; uint8_t v_addHypotheses_boxed_4840_; lean_object* v_res_4841_; 
v___x_16900__boxed_4839_ = lean_unbox(v___x_4827_);
v_addHypotheses_boxed_4840_ = lean_unbox(v_addHypotheses_4831_);
v_res_4841_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4824_, v___x_4825_, v_inductiveTypeName_4826_, v___x_16900__boxed_4839_, v___x_4828_, v___f_4829_, v_ctorName_4830_, v_addHypotheses_boxed_4840_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec(v___x_4828_);
return v_res_4841_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4844_, lean_object* v_ctorName_4845_, uint8_t v_addHypotheses_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v___f_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; uint8_t v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___f_4861_; uint8_t v___x_4862_; 
v___f_4854_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4855_ = lean_box(0);
v___x_4856_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4857_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4858_ = 1;
v___x_4859_ = lean_box(v___x_4858_);
v___x_4860_ = lean_box(v_addHypotheses_4846_);
lean_inc(v_ctorName_4845_);
v___f_4861_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4861_, 0, v___x_4856_);
lean_closure_set(v___f_4861_, 1, v___x_4857_);
lean_closure_set(v___f_4861_, 2, v_inductiveTypeName_4844_);
lean_closure_set(v___f_4861_, 3, v___x_4859_);
lean_closure_set(v___f_4861_, 4, v___x_4855_);
lean_closure_set(v___f_4861_, 5, v___f_4854_);
lean_closure_set(v___f_4861_, 6, v_ctorName_4845_);
lean_closure_set(v___f_4861_, 7, v___x_4860_);
v___x_4862_ = l_Lean_isPrivateName(v_ctorName_4845_);
lean_dec(v_ctorName_4845_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; 
v___x_4863_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4861_, v___x_4858_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
return v___x_4863_;
}
else
{
uint8_t v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = 0;
v___x_4865_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4861_, v___x_4864_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
return v___x_4865_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inductiveTypeName_4844_ = stack[0].m_obj;
lean_object* v_ctorName_4845_ = stack[1].m_obj;
uint8_t v_addHypotheses_4846_ = stack[2].m_num;
lean_object* v_a_4847_ = stack[3].m_obj;
lean_object* v_a_4848_ = stack[4].m_obj;
lean_object* v_a_4849_ = stack[5].m_obj;
lean_object* v_a_4850_ = stack[6].m_obj;
lean_object* v_a_4851_ = stack[7].m_obj;
lean_object* v_a_4852_ = stack[8].m_obj;
lean_object* v_res_4866_;
v_res_4866_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4844_, v_ctorName_4845_, v_addHypotheses_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
stack->m_obj
 = v_res_4866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4867_, lean_object* v_ctorName_4868_, lean_object* v_addHypotheses_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_){
_start:
{
uint8_t v_addHypotheses_boxed_4877_; lean_object* v_res_4878_; 
v_addHypotheses_boxed_4877_ = lean_unbox(v_addHypotheses_4869_);
v_res_4878_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4867_, v_ctorName_4868_, v_addHypotheses_boxed_4877_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
lean_dec(v_a_4875_);
lean_dec_ref(v_a_4874_);
lean_dec(v_a_4873_);
lean_dec_ref(v_a_4872_);
lean_dec(v_a_4871_);
lean_dec_ref(v_a_4870_);
return v_res_4878_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4879_, lean_object* v_ctorName_4880_, uint8_t v_addHypotheses_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4885_ = lean_box(v_addHypotheses_4881_);
v___x_4886_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4886_, 0, v_inductiveTypeName_4879_);
lean_closure_set(v___x_4886_, 1, v_ctorName_4880_);
lean_closure_set(v___x_4886_, 2, v___x_4885_);
v___x_4887_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4886_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4917_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4917_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4917_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
if (lean_obj_tag(v_a_4888_) == 0)
{
uint8_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4892_ = 0;
v___x_4893_ = lean_box(v___x_4892_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4893_);
v___x_4895_ = v___x_4890_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
else
{
lean_object* v_val_4897_; lean_object* v___x_4898_; 
lean_del_object(v___x_4890_);
v_val_4897_ = lean_ctor_get(v_a_4888_, 0);
lean_inc(v_val_4897_);
lean_dec_ref_known(v_a_4888_, 1);
v___x_4898_ = l_Lean_Elab_Command_elabCommand(v_val_4897_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4907_; 
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4907_ == 0)
{
lean_object* v_unused_4908_; 
v_unused_4908_ = lean_ctor_get(v___x_4898_, 0);
lean_dec(v_unused_4908_);
v___x_4900_ = v___x_4898_;
v_isShared_4901_ = v_isSharedCheck_4907_;
goto v_resetjp_4899_;
}
else
{
lean_dec(v___x_4898_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4907_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
uint8_t v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4905_; 
v___x_4902_ = 1;
v___x_4903_ = lean_box(v___x_4902_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v___x_4903_);
v___x_4905_ = v___x_4900_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
else
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4916_; 
v_a_4909_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4911_ = v___x_4898_;
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4898_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4914_; 
if (v_isShared_4912_ == 0)
{
v___x_4914_ = v___x_4911_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
v_a_4918_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4887_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4887_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_0interp(lean_interpreter_value* stack)
{
lean_object* v_inductiveTypeName_4879_ = stack[0].m_obj;
lean_object* v_ctorName_4880_ = stack[1].m_obj;
uint8_t v_addHypotheses_4881_ = stack[2].m_num;
lean_object* v_a_4882_ = stack[3].m_obj;
lean_object* v_a_4883_ = stack[4].m_obj;
lean_object* v_res_4926_;
v_res_4926_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4879_, v_ctorName_4880_, v_addHypotheses_4881_, v_a_4882_, v_a_4883_);
stack->m_obj
 = v_res_4926_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4927_, lean_object* v_ctorName_4928_, lean_object* v_addHypotheses_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
uint8_t v_addHypotheses_boxed_4933_; lean_object* v_res_4934_; 
v_addHypotheses_boxed_4933_ = lean_unbox(v_addHypotheses_4929_);
v_res_4934_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4927_, v_ctorName_4928_, v_addHypotheses_boxed_4933_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
return v_res_4934_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4938_, uint8_t v_addHypotheses_4939_, lean_object* v_as_x27_4940_, lean_object* v_b_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
if (lean_obj_tag(v_as_x27_4940_) == 0)
{
lean_object* v___x_4945_; 
lean_dec(v_declName_4938_);
v___x_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4945_, 0, v_b_4941_);
return v___x_4945_;
}
else
{
lean_object* v_head_4946_; lean_object* v_tail_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
lean_dec_ref(v_b_4941_);
v_head_4946_ = lean_ctor_get(v_as_x27_4940_, 0);
v_tail_4947_ = lean_ctor_get(v_as_x27_4940_, 1);
v___x_4948_ = lean_box(0);
v___x_4949_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
lean_inc(v_head_4946_);
lean_inc(v_declName_4938_);
v___x_4950_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4938_, v_head_4946_, v_addHypotheses_4939_, v___y_4942_, v___y_4943_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4962_; 
v_a_4951_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4953_ = v___x_4950_;
v_isShared_4954_ = v_isSharedCheck_4962_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4950_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4962_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
uint8_t v___x_4955_; 
v___x_4955_ = lean_unbox(v_a_4951_);
if (v___x_4955_ == 0)
{
lean_del_object(v___x_4953_);
lean_dec(v_a_4951_);
v_as_x27_4940_ = v_tail_4947_;
v_b_4941_ = v___x_4949_;
goto _start;
}
else
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4960_; 
lean_dec(v_declName_4938_);
v___x_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_a_4951_);
v___x_4958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
lean_ctor_set(v___x_4958_, 1, v___x_4948_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 0, v___x_4958_);
v___x_4960_ = v___x_4953_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v___x_4958_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
}
else
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4970_; 
lean_dec(v_declName_4938_);
v_a_4963_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4965_ = v___x_4950_;
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v___x_4950_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4968_; 
if (v_isShared_4966_ == 0)
{
v___x_4968_ = v___x_4965_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_a_4963_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
return v___x_4968_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4938_ = stack[0].m_obj;
uint8_t v_addHypotheses_4939_ = stack[1].m_num;
lean_object* v_as_x27_4940_ = stack[2].m_obj;
lean_object* v_b_4941_ = stack[3].m_obj;
lean_object* v___y_4942_ = stack[4].m_obj;
lean_object* v___y_4943_ = stack[5].m_obj;
lean_object* v_res_4971_;
v_res_4971_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4938_, v_addHypotheses_4939_, v_as_x27_4940_, v_b_4941_, v___y_4942_, v___y_4943_);
stack->m_obj
 = v_res_4971_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4972_, lean_object* v_addHypotheses_4973_, lean_object* v_as_x27_4974_, lean_object* v_b_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
uint8_t v_addHypotheses_boxed_4979_; lean_object* v_res_4980_; 
v_addHypotheses_boxed_4979_ = lean_unbox(v_addHypotheses_4973_);
v_res_4980_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4972_, v_addHypotheses_boxed_4979_, v_as_x27_4974_, v_b_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v_as_x27_4974_);
return v_res_4980_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4981_, lean_object* v_declName_4982_, uint8_t v_addHypotheses_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v_ctors_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v_ctors_4987_ = lean_ctor_get(v_a_4981_, 4);
v___x_4988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4989_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4982_, v_addHypotheses_4983_, v_ctors_4987_, v___x_4988_, v___y_4984_, v___y_4985_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_5004_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4992_ = v___x_4989_;
v_isShared_4993_ = v_isSharedCheck_5004_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4989_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_5004_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v_fst_4994_; 
v_fst_4994_ = lean_ctor_get(v_a_4990_, 0);
lean_inc(v_fst_4994_);
lean_dec(v_a_4990_);
if (lean_obj_tag(v_fst_4994_) == 0)
{
uint8_t v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4998_; 
v___x_4995_ = 0;
v___x_4996_ = lean_box(v___x_4995_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v___x_4996_);
v___x_4998_ = v___x_4992_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4996_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
else
{
lean_object* v_val_5000_; lean_object* v___x_5002_; 
v_val_5000_ = lean_ctor_get(v_fst_4994_, 0);
lean_inc(v_val_5000_);
lean_dec_ref_known(v_fst_4994_, 1);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v_val_5000_);
v___x_5002_ = v___x_4992_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_val_5000_);
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
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
v_a_5005_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4989_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4989_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4981_ = stack[0].m_obj;
lean_object* v_declName_4982_ = stack[1].m_obj;
uint8_t v_addHypotheses_4983_ = stack[2].m_num;
lean_object* v___y_4984_ = stack[3].m_obj;
lean_object* v___y_4985_ = stack[4].m_obj;
lean_object* v_res_5013_;
v_res_5013_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_4981_, v_declName_4982_, v_addHypotheses_4983_, v___y_4984_, v___y_4985_);
stack->m_obj
 = v_res_5013_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_5014_, lean_object* v_declName_5015_, lean_object* v_addHypotheses_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
uint8_t v_addHypotheses_boxed_5020_; lean_object* v_res_5021_; 
v_addHypotheses_boxed_5020_ = lean_unbox(v_addHypotheses_5016_);
v_res_5021_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5014_, v_declName_5015_, v_addHypotheses_boxed_5020_, v___y_5017_, v___y_5018_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec_ref(v_a_5014_);
return v_res_5021_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5022_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5022_);
return v___x_5023_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5024_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5025_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_5026_ = lean_unsigned_to_nat(0u);
v___x_5027_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5026_);
lean_ctor_set(v___x_5027_, 1, v___x_5026_);
lean_ctor_set(v___x_5027_, 2, v___x_5026_);
lean_ctor_set(v___x_5027_, 3, v___x_5026_);
lean_ctor_set(v___x_5027_, 4, v___x_5025_);
lean_ctor_set(v___x_5027_, 5, v___x_5025_);
lean_ctor_set(v___x_5027_, 6, v___x_5025_);
lean_ctor_set(v___x_5027_, 7, v___x_5025_);
lean_ctor_set(v___x_5027_, 8, v___x_5025_);
lean_ctor_set(v___x_5027_, 9, v___x_5025_);
lean_ctor_set(v___x_5027_, 10, v___x_5025_);
lean_ctor_set(v___x_5027_, 11, v___x_5024_);
return v___x_5027_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5028_ = lean_unsigned_to_nat(32u);
v___x_5029_ = lean_mk_empty_array_with_capacity(v___x_5028_);
v___x_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5029_);
return v___x_5030_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
size_t v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5031_ = ((size_t)5ULL);
v___x_5032_ = lean_unsigned_to_nat(0u);
v___x_5033_ = lean_unsigned_to_nat(32u);
v___x_5034_ = lean_mk_empty_array_with_capacity(v___x_5033_);
v___x_5035_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_5036_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
lean_ctor_set(v___x_5036_, 1, v___x_5034_);
lean_ctor_set(v___x_5036_, 2, v___x_5032_);
lean_ctor_set(v___x_5036_, 3, v___x_5032_);
lean_ctor_set_usize(v___x_5036_, 4, v___x_5031_);
return v___x_5036_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5037_ = lean_box(1);
v___x_5038_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_5039_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_5040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5039_);
lean_ctor_set(v___x_5040_, 1, v___x_5038_);
lean_ctor_set(v___x_5040_, 2, v___x_5037_);
return v___x_5040_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v___x_5044_; lean_object* v_env_5045_; uint8_t v___x_5046_; lean_object* v_env_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v_scopes_5050_; lean_object* v___x_5051_; lean_object* v_opts_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5044_ = lean_st_ref_get(v___y_5042_);
v_env_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc_ref(v_env_5045_);
lean_dec(v___x_5044_);
v___x_5046_ = 0;
v_env_5047_ = l_Lean_Environment_setRecordingDeps(v_env_5045_, v___x_5046_);
v___x_5048_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5049_ = lean_st_ref_get(v___y_5042_);
v_scopes_5050_ = lean_ctor_get(v___x_5049_, 2);
lean_inc(v_scopes_5050_);
lean_dec(v___x_5049_);
v___x_5051_ = l_List_head_x21___redArg(v___x_5048_, v_scopes_5050_);
lean_dec(v_scopes_5050_);
v_opts_5052_ = lean_ctor_get(v___x_5051_, 1);
lean_inc_ref(v_opts_5052_);
lean_dec(v___x_5051_);
v___x_5053_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_5054_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_5055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5055_, 0, v_env_5047_);
lean_ctor_set(v___x_5055_, 1, v___x_5053_);
lean_ctor_set(v___x_5055_, 2, v___x_5054_);
lean_ctor_set(v___x_5055_, 3, v_opts_5052_);
v___x_5056_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
lean_ctor_set(v___x_5056_, 1, v_msgData_5041_);
v___x_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
return v___x_5057_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_5041_ = stack[0].m_obj;
lean_object* v___y_5042_ = stack[1].m_obj;
lean_object* v_res_5058_;
v_res_5058_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5041_, v___y_5042_);
stack->m_obj
 = v_res_5058_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5059_, v___y_5060_);
lean_dec(v___y_5060_);
return v_res_5062_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_5063_, lean_object* v_macroStack_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v_scopes_5069_; lean_object* v___x_5070_; lean_object* v_opts_5071_; lean_object* v___x_5072_; uint8_t v___x_5073_; 
v___x_5067_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5068_ = lean_st_ref_get(v___y_5065_);
v_scopes_5069_ = lean_ctor_get(v___x_5068_, 2);
lean_inc(v_scopes_5069_);
lean_dec(v___x_5068_);
v___x_5070_ = l_List_head_x21___redArg(v___x_5067_, v_scopes_5069_);
lean_dec(v_scopes_5069_);
v_opts_5071_ = lean_ctor_get(v___x_5070_, 1);
lean_inc_ref(v_opts_5071_);
lean_dec(v___x_5070_);
v___x_5072_ = l_Lean_Elab_pp_macroStack;
v___x_5073_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_5071_, v___x_5072_);
lean_dec_ref(v_opts_5071_);
if (v___x_5073_ == 0)
{
lean_object* v___x_5074_; 
lean_dec(v_macroStack_5064_);
v___x_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5074_, 0, v_msgData_5063_);
return v___x_5074_;
}
else
{
if (lean_obj_tag(v_macroStack_5064_) == 0)
{
lean_object* v___x_5075_; 
v___x_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5075_, 0, v_msgData_5063_);
return v___x_5075_;
}
else
{
lean_object* v_head_5076_; lean_object* v_after_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5092_; 
v_head_5076_ = lean_ctor_get(v_macroStack_5064_, 0);
lean_inc(v_head_5076_);
v_after_5077_ = lean_ctor_get(v_head_5076_, 1);
v_isSharedCheck_5092_ = !lean_is_exclusive(v_head_5076_);
if (v_isSharedCheck_5092_ == 0)
{
lean_object* v_unused_5093_; 
v_unused_5093_ = lean_ctor_get(v_head_5076_, 0);
lean_dec(v_unused_5093_);
v___x_5079_ = v_head_5076_;
v_isShared_5080_ = v_isSharedCheck_5092_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_after_5077_);
lean_dec(v_head_5076_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5092_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5081_; lean_object* v___x_5083_; 
v___x_5081_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_5080_ == 0)
{
lean_ctor_set_tag(v___x_5079_, 7);
lean_ctor_set(v___x_5079_, 1, v___x_5081_);
lean_ctor_set(v___x_5079_, 0, v_msgData_5063_);
v___x_5083_ = v___x_5079_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_msgData_5063_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v_msgData_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___x_5084_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_5085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5083_);
lean_ctor_set(v___x_5085_, 1, v___x_5084_);
v___x_5086_ = l_Lean_MessageData_ofSyntax(v_after_5077_);
v___x_5087_ = l_Lean_indentD(v___x_5086_);
v_msgData_5088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5088_, 0, v___x_5085_);
lean_ctor_set(v_msgData_5088_, 1, v___x_5087_);
v___x_5089_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_5088_, v_macroStack_5064_);
v___x_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5089_);
return v___x_5090_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_5063_ = stack[0].m_obj;
lean_object* v_macroStack_5064_ = stack[1].m_obj;
lean_object* v___y_5065_ = stack[2].m_obj;
lean_object* v_res_5094_;
v_res_5094_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5063_, v_macroStack_5064_, v___y_5065_);
stack->m_obj
 = v_res_5094_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_5095_, lean_object* v_macroStack_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5095_, v_macroStack_5096_, v___y_5097_);
lean_dec(v___y_5097_);
return v_res_5099_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Elab_Command_getRef___redArg(v___y_5101_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v_macroStack_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v_a_5109_; lean_object* v___x_5110_; lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5119_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5105_);
lean_dec_ref_known(v___x_5104_, 1);
v_macroStack_5106_ = lean_ctor_get(v___y_5101_, 4);
v___x_5107_ = l_Lean_Elab_getBetterRef(v_a_5105_, v_macroStack_5106_);
lean_dec(v_a_5105_);
v___x_5108_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_5100_, v___y_5102_);
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref(v___x_5108_);
lean_inc(v_macroStack_5106_);
v___x_5110_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_5109_, v_macroStack_5106_, v___y_5102_);
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5113_ = v___x_5110_;
v_isShared_5114_ = v_isSharedCheck_5119_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5110_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5119_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; lean_object* v___x_5117_; 
v___x_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5115_, 0, v___x_5107_);
lean_ctor_set(v___x_5115_, 1, v_a_5111_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set_tag(v___x_5113_, 1);
lean_ctor_set(v___x_5113_, 0, v___x_5115_);
v___x_5117_ = v___x_5113_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5115_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
lean_dec_ref(v_msg_5100_);
v_a_5120_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5104_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5104_);
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
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5100_ = stack[0].m_obj;
lean_object* v___y_5101_ = stack[1].m_obj;
lean_object* v___y_5102_ = stack[2].m_obj;
lean_object* v_res_5128_;
v_res_5128_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5100_, v___y_5101_, v___y_5102_);
stack->m_obj
 = v_res_5128_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5129_, v___y_5130_, v___y_5131_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
return v_res_5133_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v___x_5138_; lean_object* v_env_5139_; lean_object* v___x_5140_; 
v___x_5138_ = lean_st_ref_get(v___y_5136_);
v_env_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc_ref(v_env_5139_);
lean_dec(v___x_5138_);
lean_inc(v_constName_5134_);
v___x_5140_ = l_Lean_isInductiveCore_x3f(v_env_5139_, v_constName_5134_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v___x_5141_; uint8_t v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5141_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5142_ = 0;
v___x_5143_ = l_Lean_MessageData_ofConstName(v_constName_5134_, v___x_5142_);
v___x_5144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5144_, 0, v___x_5141_);
lean_ctor_set(v___x_5144_, 1, v___x_5143_);
v___x_5145_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5144_);
lean_ctor_set(v___x_5146_, 1, v___x_5145_);
v___x_5147_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5146_, v___y_5135_, v___y_5136_);
return v___x_5147_;
}
else
{
lean_object* v_val_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
lean_dec(v_constName_5134_);
v_val_5148_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_5140_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_val_5148_);
lean_dec(v___x_5140_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set_tag(v___x_5150_, 0);
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_val_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_5134_ = stack[0].m_obj;
lean_object* v___y_5135_ = stack[1].m_obj;
lean_object* v___y_5136_ = stack[2].m_obj;
lean_object* v_res_5156_;
v_res_5156_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5134_, v___y_5135_, v___y_5136_);
stack->m_obj
 = v_res_5156_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5157_, v___y_5158_, v___y_5159_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
return v_res_5161_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5163_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5164_ = l_Lean_stringToMessageData(v___x_5163_);
return v___x_5164_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
lean_object* v___x_5172_; 
lean_inc(v_declName_5165_);
v___x_5172_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5165_, v___y_5166_, v___y_5167_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; uint8_t v___x_5174_; lean_object* v___x_5175_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
lean_dec_ref_known(v___x_5172_, 1);
v___x_5174_ = 0;
lean_inc(v_declName_5165_);
v___x_5175_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5173_, v_declName_5165_, v___x_5174_, v___y_5166_, v___y_5167_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v_a_5176_; uint8_t v___x_5177_; 
v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
lean_inc(v_a_5176_);
lean_dec_ref_known(v___x_5175_, 1);
v___x_5177_ = lean_unbox(v_a_5176_);
lean_dec(v_a_5176_);
if (v___x_5177_ == 0)
{
uint8_t v___x_5178_; lean_object* v___x_5179_; 
v___x_5178_ = 1;
lean_inc(v_declName_5165_);
v___x_5179_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5173_, v_declName_5165_, v___x_5178_, v___y_5166_, v___y_5167_);
lean_dec(v_a_5173_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; uint8_t v___x_5181_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_a_5180_);
lean_dec_ref_known(v___x_5179_, 1);
v___x_5181_ = lean_unbox(v_a_5180_);
lean_dec(v_a_5180_);
if (v___x_5181_ == 0)
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5182_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5183_ = l_Lean_MessageData_ofConstName(v_declName_5165_, v___x_5174_);
v___x_5184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5182_);
lean_ctor_set(v___x_5184_, 1, v___x_5183_);
v___x_5185_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5184_);
lean_ctor_set(v___x_5186_, 1, v___x_5185_);
v___x_5187_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5186_, v___y_5166_, v___y_5167_);
return v___x_5187_;
}
else
{
lean_dec(v_declName_5165_);
goto v___jp_5169_;
}
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
lean_dec(v_declName_5165_);
v_a_5188_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5179_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5179_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
else
{
lean_dec(v_a_5173_);
lean_dec(v_declName_5165_);
goto v___jp_5169_;
}
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
lean_dec(v_a_5173_);
lean_dec(v_declName_5165_);
v_a_5196_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5175_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5175_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
else
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5211_; 
lean_dec(v_declName_5165_);
v_a_5204_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5211_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5211_ == 0)
{
v___x_5206_ = v___x_5172_;
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5172_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5209_; 
if (v_isShared_5207_ == 0)
{
v___x_5209_ = v___x_5206_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v_a_5204_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
}
v___jp_5169_:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; 
v___x_5170_ = lean_box(0);
v___x_5171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
return v___x_5171_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_5165_ = stack[0].m_obj;
lean_object* v___y_5166_ = stack[1].m_obj;
lean_object* v___y_5167_ = stack[2].m_obj;
lean_object* v_res_5212_;
v_res_5212_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5165_, v___y_5166_, v___y_5167_);
stack->m_obj
 = v_res_5212_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5213_, v___y_5214_, v___y_5215_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
return v_res_5217_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_){
_start:
{
lean_object* v___f_5222_; lean_object* v___x_5223_; 
lean_inc(v_declName_5218_);
v___f_5222_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5222_, 0, v_declName_5218_);
v___x_5223_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5218_, v___f_5222_, v_a_5219_, v_a_5220_);
return v___x_5223_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_5218_ = stack[0].m_obj;
lean_object* v_a_5219_ = stack[1].m_obj;
lean_object* v_a_5220_ = stack[2].m_obj;
lean_object* v_res_5224_;
v_res_5224_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5218_, v_a_5219_, v_a_5220_);
stack->m_obj
 = v_res_5224_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5225_, v_a_5226_, v_a_5227_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
return v_res_5229_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5230_, uint8_t v_addHypotheses_5231_, lean_object* v_as_5232_, lean_object* v_as_x27_5233_, lean_object* v_b_5234_, lean_object* v_a_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v___x_5239_; 
v___x_5239_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5230_, v_addHypotheses_5231_, v_as_x27_5233_, v_b_5234_, v___y_5236_, v___y_5237_);
return v___x_5239_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_5230_ = stack[0].m_obj;
uint8_t v_addHypotheses_5231_ = stack[1].m_num;
lean_object* v_as_5232_ = stack[2].m_obj;
lean_object* v_as_x27_5233_ = stack[3].m_obj;
lean_object* v_b_5234_ = stack[4].m_obj;
lean_object* v___y_5236_ = stack[6].m_obj;
lean_object* v___y_5237_ = stack[7].m_obj;
lean_object* v_res_5240_;
v_res_5240_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5230_, v_addHypotheses_5231_, v_as_5232_, v_as_x27_5233_, v_b_5234_, lean_box(0), v___y_5236_, v___y_5237_);
stack->m_obj
 = v_res_5240_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5241_, lean_object* v_addHypotheses_5242_, lean_object* v_as_5243_, lean_object* v_as_x27_5244_, lean_object* v_b_5245_, lean_object* v_a_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
uint8_t v_addHypotheses_boxed_5250_; lean_object* v_res_5251_; 
v_addHypotheses_boxed_5250_ = lean_unbox(v_addHypotheses_5242_);
v_res_5251_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5241_, v_addHypotheses_boxed_5250_, v_as_5243_, v_as_x27_5244_, v_b_5245_, v_a_5246_, v___y_5247_, v___y_5248_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v_as_x27_5244_);
lean_dec(v_as_5243_);
return v_res_5251_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v___x_5256_; 
v___x_5256_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5252_, v___y_5254_);
return v___x_5256_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_5252_ = stack[0].m_obj;
lean_object* v___y_5253_ = stack[1].m_obj;
lean_object* v___y_5254_ = stack[2].m_obj;
lean_object* v_res_5257_;
v_res_5257_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5252_, v___y_5253_, v___y_5254_);
stack->m_obj
 = v_res_5257_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5258_, v___y_5259_, v___y_5260_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
return v_res_5262_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5263_, lean_object* v_msg_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5264_, v___y_5265_, v___y_5266_);
return v___x_5268_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5264_ = stack[1].m_obj;
lean_object* v___y_5265_ = stack[2].m_obj;
lean_object* v___y_5266_ = stack[3].m_obj;
lean_object* v_res_5269_;
v_res_5269_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_box(0), v_msg_5264_, v___y_5265_, v___y_5266_);
stack->m_obj
 = v_res_5269_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5270_, lean_object* v_msg_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v_res_5275_; 
v_res_5275_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5270_, v_msg_5271_, v___y_5272_, v___y_5273_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
return v_res_5275_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5276_, lean_object* v_macroStack_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
lean_object* v___x_5281_; 
v___x_5281_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5276_, v_macroStack_5277_, v___y_5279_);
return v___x_5281_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_5276_ = stack[0].m_obj;
lean_object* v_macroStack_5277_ = stack[1].m_obj;
lean_object* v___y_5278_ = stack[2].m_obj;
lean_object* v___y_5279_ = stack[3].m_obj;
lean_object* v_res_5282_;
v_res_5282_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5276_, v_macroStack_5277_, v___y_5278_, v___y_5279_);
stack->m_obj
 = v_res_5282_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5283_, lean_object* v_macroStack_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5283_, v_macroStack_5284_, v___y_5285_, v___y_5286_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
return v_res_5288_;
}
}
lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v___x_5292_; lean_object* v_env_5293_; uint8_t v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5292_ = lean_st_ref_get(v___y_5290_);
v_env_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc_ref(v_env_5293_);
lean_dec(v___x_5292_);
v___x_5294_ = l_Lean_isInductiveCore(v_env_5293_, v_declName_5289_);
v___x_5295_ = lean_box(v___x_5294_);
v___x_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5295_);
return v___x_5296_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_5289_ = stack[0].m_obj;
lean_object* v___y_5290_ = stack[1].m_obj;
lean_object* v_res_5297_;
v_res_5297_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5289_, v___y_5290_);
stack->m_obj
 = v_res_5297_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5298_, v___y_5299_);
lean_dec(v___y_5299_);
return v_res_5301_;
}
}
lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
lean_object* v___x_5306_; 
v___x_5306_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5302_, v___y_5304_);
return v___x_5306_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_5302_ = stack[0].m_obj;
lean_object* v___y_5303_ = stack[1].m_obj;
lean_object* v___y_5304_ = stack[2].m_obj;
lean_object* v_res_5307_;
v_res_5307_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5302_, v___y_5303_, v___y_5304_);
stack->m_obj
 = v_res_5307_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5308_, v___y_5309_, v___y_5310_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
return v_res_5312_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
if (v_____do__lift_5313_ == 0)
{
uint8_t v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; 
v___x_5317_ = 1;
v___x_5318_ = lean_box(v___x_5317_);
v___x_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5318_);
return v___x_5319_;
}
else
{
uint8_t v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5320_ = 0;
v___x_5321_ = lean_box(v___x_5320_);
v___x_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5321_);
return v___x_5322_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_5313_ = stack[0].m_num;
lean_object* v___y_5314_ = stack[1].m_obj;
lean_object* v___y_5315_ = stack[2].m_obj;
lean_object* v_res_5323_;
v_res_5323_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_5313_, v___y_5314_, v___y_5315_);
stack->m_obj
 = v_res_5323_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
uint8_t v_____do__lift_1606__boxed_5328_; lean_object* v_res_5329_; 
v_____do__lift_1606__boxed_5328_ = lean_unbox(v_____do__lift_5324_);
v_res_5329_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1606__boxed_5328_, v___y_5325_, v___y_5326_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
return v_res_5329_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5330_, size_t v_i_5331_, size_t v_stop_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
uint8_t v___x_5340_; 
v___x_5340_ = lean_usize_dec_eq(v_i_5331_, v_stop_5332_);
if (v___x_5340_ == 0)
{
uint8_t v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; 
v___x_5341_ = 1;
v___x_5342_ = lean_array_uget_borrowed(v_as_5330_, v_i_5331_);
lean_inc(v___x_5342_);
v___x_5343_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5342_, v___y_5334_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5353_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5346_ = v___x_5343_;
v_isShared_5347_ = v_isSharedCheck_5353_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5343_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5353_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
uint8_t v___x_5348_; 
v___x_5348_ = lean_unbox(v_a_5344_);
lean_dec(v_a_5344_);
if (v___x_5348_ == 0)
{
lean_object* v___x_5349_; lean_object* v___x_5351_; 
v___x_5349_ = lean_box(v___x_5341_);
if (v_isShared_5347_ == 0)
{
lean_ctor_set(v___x_5346_, 0, v___x_5349_);
v___x_5351_ = v___x_5346_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5349_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
else
{
lean_del_object(v___x_5346_);
goto v___jp_5336_;
}
}
}
else
{
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5363_; 
v_a_5354_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5356_ = v___x_5343_;
v_isShared_5357_ = v_isSharedCheck_5363_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5343_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5363_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
uint8_t v___x_5358_; 
v___x_5358_ = lean_unbox(v_a_5354_);
lean_dec(v_a_5354_);
if (v___x_5358_ == 0)
{
lean_del_object(v___x_5356_);
goto v___jp_5336_;
}
else
{
lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5359_ = lean_box(v___x_5341_);
if (v_isShared_5357_ == 0)
{
lean_ctor_set_tag(v___x_5356_, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5359_);
v___x_5361_ = v___x_5356_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
else
{
return v___x_5343_;
}
}
}
else
{
uint8_t v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5364_ = 0;
v___x_5365_ = lean_box(v___x_5364_);
v___x_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5366_, 0, v___x_5365_);
return v___x_5366_;
}
v___jp_5336_:
{
size_t v___x_5337_; size_t v___x_5338_; 
v___x_5337_ = ((size_t)1ULL);
v___x_5338_ = lean_usize_add(v_i_5331_, v___x_5337_);
v_i_5331_ = v___x_5338_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5330_ = stack[0].m_obj;
size_t v_i_5331_ = stack[1].m_num;
size_t v_stop_5332_ = stack[2].m_num;
lean_object* v___y_5333_ = stack[3].m_obj;
lean_object* v___y_5334_ = stack[4].m_obj;
lean_object* v_res_5367_;
v_res_5367_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5330_, v_i_5331_, v_stop_5332_, v___y_5333_, v___y_5334_);
stack->m_obj
 = v_res_5367_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5368_, lean_object* v_i_5369_, lean_object* v_stop_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
size_t v_i_boxed_5374_; size_t v_stop_boxed_5375_; lean_object* v_res_5376_; 
v_i_boxed_5374_ = lean_unbox_usize(v_i_5369_);
lean_dec(v_i_5369_);
v_stop_boxed_5375_ = lean_unbox_usize(v_stop_5370_);
lean_dec(v_stop_5370_);
v_res_5376_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5368_, v_i_boxed_5374_, v_stop_boxed_5375_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5368_);
return v_res_5376_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5377_, size_t v_i_5378_, size_t v_stop_5379_, lean_object* v_b_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
uint8_t v___x_5384_; 
v___x_5384_ = lean_usize_dec_eq(v_i_5378_, v_stop_5379_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5385_ = lean_array_uget_borrowed(v_as_5377_, v_i_5378_);
lean_inc(v___x_5385_);
v___x_5386_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5385_, v___y_5381_, v___y_5382_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v_a_5387_; size_t v___x_5388_; size_t v___x_5389_; 
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref_known(v___x_5386_, 1);
v___x_5388_ = ((size_t)1ULL);
v___x_5389_ = lean_usize_add(v_i_5378_, v___x_5388_);
v_i_5378_ = v___x_5389_;
v_b_5380_ = v_a_5387_;
goto _start;
}
else
{
return v___x_5386_;
}
}
else
{
lean_object* v___x_5391_; 
v___x_5391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5391_, 0, v_b_5380_);
return v___x_5391_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5377_ = stack[0].m_obj;
size_t v_i_5378_ = stack[1].m_num;
size_t v_stop_5379_ = stack[2].m_num;
lean_object* v_b_5380_ = stack[3].m_obj;
lean_object* v___y_5381_ = stack[4].m_obj;
lean_object* v___y_5382_ = stack[5].m_obj;
lean_object* v_res_5392_;
v_res_5392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5377_, v_i_5378_, v_stop_5379_, v_b_5380_, v___y_5381_, v___y_5382_);
stack->m_obj
 = v_res_5392_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5393_, lean_object* v_i_5394_, lean_object* v_stop_5395_, lean_object* v_b_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
size_t v_i_boxed_5400_; size_t v_stop_boxed_5401_; lean_object* v_res_5402_; 
v_i_boxed_5400_ = lean_unbox_usize(v_i_5394_);
lean_dec(v_i_5394_);
v_stop_boxed_5401_ = lean_unbox_usize(v_stop_5395_);
lean_dec(v_stop_5395_);
v_res_5402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5393_, v_i_boxed_5400_, v_stop_boxed_5401_, v_b_5396_, v___y_5397_, v___y_5398_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
lean_dec_ref(v_as_5393_);
return v_res_5402_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_){
_start:
{
uint8_t v___y_5408_; lean_object* v___y_5409_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___y_5445_; uint8_t v___x_5448_; 
v___x_5427_ = lean_unsigned_to_nat(0u);
v___x_5428_ = lean_array_get_size(v_declNames_5403_);
v___x_5448_ = lean_nat_dec_lt(v___x_5427_, v___x_5428_);
if (v___x_5448_ == 0)
{
lean_object* v___x_5449_; 
v___x_5449_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5448_, v_a_5404_, v_a_5405_);
v___y_5445_ = v___x_5449_;
goto v___jp_5444_;
}
else
{
if (v___x_5448_ == 0)
{
goto v___jp_5429_;
}
else
{
size_t v___x_5450_; size_t v___x_5451_; lean_object* v___x_5452_; 
v___x_5450_ = ((size_t)0ULL);
v___x_5451_ = lean_usize_of_nat(v___x_5428_);
v___x_5452_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5403_, v___x_5450_, v___x_5451_, v_a_5404_, v_a_5405_);
if (lean_obj_tag(v___x_5452_) == 0)
{
lean_object* v_a_5453_; uint8_t v___x_5454_; lean_object* v___x_5455_; 
v_a_5453_ = lean_ctor_get(v___x_5452_, 0);
lean_inc(v_a_5453_);
lean_dec_ref_known(v___x_5452_, 1);
v___x_5454_ = lean_unbox(v_a_5453_);
lean_dec(v_a_5453_);
v___x_5455_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5454_, v_a_5404_, v_a_5405_);
v___y_5445_ = v___x_5455_;
goto v___jp_5444_;
}
else
{
v___y_5445_ = v___x_5452_;
goto v___jp_5444_;
}
}
}
v___jp_5407_:
{
if (lean_obj_tag(v___y_5409_) == 0)
{
lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5417_; 
v_isSharedCheck_5417_ = !lean_is_exclusive(v___y_5409_);
if (v_isSharedCheck_5417_ == 0)
{
lean_object* v_unused_5418_; 
v_unused_5418_ = lean_ctor_get(v___y_5409_, 0);
lean_dec(v_unused_5418_);
v___x_5411_ = v___y_5409_;
v_isShared_5412_ = v_isSharedCheck_5417_;
goto v_resetjp_5410_;
}
else
{
lean_dec(v___y_5409_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5417_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5413_; lean_object* v___x_5415_; 
v___x_5413_ = lean_box(v___y_5408_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v___x_5413_);
v___x_5415_ = v___x_5411_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5413_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
return v___x_5415_;
}
}
}
else
{
lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
v_a_5419_ = lean_ctor_get(v___y_5409_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___y_5409_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5421_ = v___y_5409_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_dec(v___y_5409_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5424_; 
if (v_isShared_5422_ == 0)
{
v___x_5424_ = v___x_5421_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5419_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
v___jp_5429_:
{
uint8_t v___x_5430_; uint8_t v___x_5431_; 
v___x_5430_ = 1;
v___x_5431_ = lean_nat_dec_lt(v___x_5427_, v___x_5428_);
if (v___x_5431_ == 0)
{
lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5432_ = lean_box(v___x_5430_);
v___x_5433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5432_);
return v___x_5433_;
}
else
{
lean_object* v___x_5434_; uint8_t v___x_5435_; 
v___x_5434_ = lean_box(0);
v___x_5435_ = lean_nat_dec_le(v___x_5428_, v___x_5428_);
if (v___x_5435_ == 0)
{
if (v___x_5431_ == 0)
{
lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5436_ = lean_box(v___x_5430_);
v___x_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5436_);
return v___x_5437_;
}
else
{
size_t v___x_5438_; size_t v___x_5439_; lean_object* v___x_5440_; 
v___x_5438_ = ((size_t)0ULL);
v___x_5439_ = lean_usize_of_nat(v___x_5428_);
v___x_5440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5403_, v___x_5438_, v___x_5439_, v___x_5434_, v_a_5404_, v_a_5405_);
v___y_5408_ = v___x_5430_;
v___y_5409_ = v___x_5440_;
goto v___jp_5407_;
}
}
else
{
size_t v___x_5441_; size_t v___x_5442_; lean_object* v___x_5443_; 
v___x_5441_ = ((size_t)0ULL);
v___x_5442_ = lean_usize_of_nat(v___x_5428_);
v___x_5443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5403_, v___x_5441_, v___x_5442_, v___x_5434_, v_a_5404_, v_a_5405_);
v___y_5408_ = v___x_5430_;
v___y_5409_ = v___x_5443_;
goto v___jp_5407_;
}
}
}
v___jp_5444_:
{
if (lean_obj_tag(v___y_5445_) == 0)
{
lean_object* v_a_5446_; uint8_t v___x_5447_; 
v_a_5446_ = lean_ctor_get(v___y_5445_, 0);
v___x_5447_ = lean_unbox(v_a_5446_);
if (v___x_5447_ == 0)
{
return v___y_5445_;
}
else
{
lean_dec_ref_known(v___y_5445_, 1);
goto v___jp_5429_;
}
}
else
{
return v___y_5445_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInhabitedInstanceHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_5403_ = stack[0].m_obj;
lean_object* v_a_5404_ = stack[1].m_obj;
lean_object* v_a_5405_ = stack[2].m_obj;
lean_object* v_res_5456_;
v_res_5456_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5403_, v_a_5404_, v_a_5405_);
stack->m_obj
 = v_res_5456_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_){
_start:
{
lean_object* v_res_5461_; 
v_res_5461_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5457_, v_a_5458_, v_a_5459_);
lean_dec(v_a_5459_);
lean_dec_ref(v_a_5458_);
lean_dec_ref(v_declNames_5457_);
return v_res_5461_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; 
v___x_5526_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5527_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5528_ = l_Lean_Elab_registerDerivingHandler(v___x_5526_, v___x_5527_);
if (lean_obj_tag(v___x_5528_) == 0)
{
lean_object* v___x_5529_; uint8_t v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; 
lean_dec_ref_known(v___x_5528_, 1);
v___x_5529_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5530_ = 0;
v___x_5531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5532_ = l_Lean_registerTraceClass(v___x_5529_, v___x_5530_, v___x_5531_);
return v___x_5532_;
}
else
{
return v___x_5528_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5533_;
v_res_5533_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5533_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5535_;
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
