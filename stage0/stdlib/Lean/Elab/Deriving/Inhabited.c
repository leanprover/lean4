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
v___x_496_ = lean_nat_add(v___y_493_, v___y_495_);
lean_dec(v___y_495_);
lean_dec(v___y_493_);
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
lean_ctor_set(v___x_476_, 3, v___y_494_);
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
lean_ctor_set(v_reuseFailAlloc_501_, 3, v___y_494_);
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
v___y_493_ = v___x_508_;
v___y_494_ = v___x_507_;
v___y_495_ = v_size_509_;
goto v___jp_492_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___y_493_ = v___x_508_;
v___y_494_ = v___x_507_;
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
lean_object* v_toCold_1975_; lean_object* v_currRecDepth_1976_; lean_object* v_ref_1977_; uint16_t v_optionFlags_1978_; uint8_t v_suppressElabErrors_1979_; uint8_t v_isRecordingDeps_1980_; lean_object* v_ref_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_traceState_1984_; lean_object* v_traces_1985_; lean_object* v___x_1986_; size_t v_sz_1987_; size_t v___x_1988_; lean_object* v___x_1989_; lean_object* v_msg_1990_; lean_object* v___x_1991_; lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2030_; 
v_toCold_1975_ = lean_ctor_get(v___y_1972_, 0);
v_currRecDepth_1976_ = lean_ctor_get(v___y_1972_, 1);
v_ref_1977_ = lean_ctor_get(v___y_1972_, 2);
v_optionFlags_1978_ = lean_ctor_get_uint16(v___y_1972_, sizeof(void*)*3);
v_suppressElabErrors_1979_ = lean_ctor_get_uint8(v___y_1972_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1980_ = lean_ctor_get_uint8(v___y_1972_, sizeof(void*)*3 + 3);
v_ref_1981_ = l_Lean_replaceRef(v_ref_1968_, v_ref_1977_);
lean_inc(v_currRecDepth_1976_);
lean_inc_ref(v_toCold_1975_);
v___x_1982_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1982_, 0, v_toCold_1975_);
lean_ctor_set(v___x_1982_, 1, v_currRecDepth_1976_);
lean_ctor_set(v___x_1982_, 2, v_ref_1981_);
lean_ctor_set_uint16(v___x_1982_, sizeof(void*)*3, v_optionFlags_1978_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*3 + 2, v_suppressElabErrors_1979_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*3 + 3, v_isRecordingDeps_1980_);
v___x_1983_ = lean_st_ref_get(v___y_1973_);
v_traceState_1984_ = lean_ctor_get(v___x_1983_, 4);
lean_inc_ref(v_traceState_1984_);
lean_dec(v___x_1983_);
v_traces_1985_ = lean_ctor_get(v_traceState_1984_, 0);
lean_inc_ref(v_traces_1985_);
lean_dec_ref(v_traceState_1984_);
v___x_1986_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1985_);
lean_dec_ref(v_traces_1985_);
v_sz_1987_ = lean_array_size(v___x_1986_);
v___x_1988_ = ((size_t)0ULL);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_1987_, v___x_1988_, v___x_1986_);
v_msg_1990_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1990_, 0, v_data_1967_);
lean_ctor_set(v_msg_1990_, 1, v_msg_1969_);
lean_ctor_set(v_msg_1990_, 2, v___x_1989_);
v___x_1991_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1990_, v___y_1970_, v___y_1971_, v___x_1982_, v___y_1973_);
lean_dec_ref_known(v___x_1982_, 3);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2030_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2030_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v_traceState_1997_; lean_object* v_env_1998_; lean_object* v_nextMacroScope_1999_; lean_object* v_ngen_2000_; lean_object* v_auxDeclNGen_2001_; lean_object* v_cache_2002_; lean_object* v_recordedDeps_2003_; lean_object* v_messages_2004_; lean_object* v_infoState_2005_; lean_object* v_snapshotTasks_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2029_; 
v___x_1996_ = lean_st_ref_take(v___y_1973_);
v_traceState_1997_ = lean_ctor_get(v___x_1996_, 4);
v_env_1998_ = lean_ctor_get(v___x_1996_, 0);
v_nextMacroScope_1999_ = lean_ctor_get(v___x_1996_, 1);
v_ngen_2000_ = lean_ctor_get(v___x_1996_, 2);
v_auxDeclNGen_2001_ = lean_ctor_get(v___x_1996_, 3);
v_cache_2002_ = lean_ctor_get(v___x_1996_, 5);
v_recordedDeps_2003_ = lean_ctor_get(v___x_1996_, 6);
v_messages_2004_ = lean_ctor_get(v___x_1996_, 7);
v_infoState_2005_ = lean_ctor_get(v___x_1996_, 8);
v_snapshotTasks_2006_ = lean_ctor_get(v___x_1996_, 9);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2008_ = v___x_1996_;
v_isShared_2009_ = v_isSharedCheck_2029_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_snapshotTasks_2006_);
lean_inc(v_infoState_2005_);
lean_inc(v_messages_2004_);
lean_inc(v_recordedDeps_2003_);
lean_inc(v_cache_2002_);
lean_inc(v_traceState_1997_);
lean_inc(v_auxDeclNGen_2001_);
lean_inc(v_ngen_2000_);
lean_inc(v_nextMacroScope_1999_);
lean_inc(v_env_1998_);
lean_dec(v___x_1996_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2029_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
uint64_t v_tid_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2027_; 
v_tid_2010_ = lean_ctor_get_uint64(v_traceState_1997_, sizeof(void*)*1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_traceState_1997_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v_traceState_1997_, 0);
lean_dec(v_unused_2028_);
v___x_2012_ = v_traceState_1997_;
v_isShared_2013_ = v_isSharedCheck_2027_;
goto v_resetjp_2011_;
}
else
{
lean_dec(v_traceState_1997_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2027_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_ref_1968_);
lean_ctor_set(v___x_2015_, 1, v_a_1992_);
v___x_2016_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1966_, v___x_2015_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2016_);
lean_ctor_set_uint64(v_reuseFailAlloc_2026_, sizeof(void*)*1, v_tid_2010_);
v___x_2018_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v___x_2018_);
v___x_2020_ = v___x_2008_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_env_1998_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_nextMacroScope_1999_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_ngen_2000_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_auxDeclNGen_2001_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2025_, 5, v_cache_2002_);
lean_ctor_set(v_reuseFailAlloc_2025_, 6, v_recordedDeps_2003_);
lean_ctor_set(v_reuseFailAlloc_2025_, 7, v_messages_2004_);
lean_ctor_set(v_reuseFailAlloc_2025_, 8, v_infoState_2005_);
lean_ctor_set(v_reuseFailAlloc_2025_, 9, v_snapshotTasks_2006_);
v___x_2020_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_st_ref_put(v___y_1973_, v___x_2020_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2014_);
v___x_2023_ = v___x_1994_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2014_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg___boxed(lean_object* v_oldTraces_2031_, lean_object* v_data_2032_, lean_object* v_ref_2033_, lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2031_, v_data_2032_, v_ref_2033_, v_msg_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2040_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0));
v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
return v___x_2043_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2044_; double v___x_2045_; 
v___x_2044_ = lean_unsigned_to_nat(1000u);
v___x_2045_ = lean_float_of_nat(v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object* v_cls_2046_, uint8_t v_collapsed_2047_, lean_object* v_tag_2048_, lean_object* v_opts_2049_, uint8_t v_clsEnabled_2050_, lean_object* v_oldTraces_2051_, lean_object* v_msg_2052_, lean_object* v_resStartStop_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_fst_2061_; lean_object* v_snd_2062_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v_data_2066_; lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___y_2074_; lean_object* v_a_2075_; uint8_t v___y_2090_; double v___y_2122_; 
v_fst_2061_ = lean_ctor_get(v_resStartStop_2053_, 0);
lean_inc(v_fst_2061_);
v_snd_2062_ = lean_ctor_get(v_resStartStop_2053_, 1);
lean_inc(v_snd_2062_);
lean_dec_ref(v_resStartStop_2053_);
v_fst_2069_ = lean_ctor_get(v_snd_2062_, 0);
lean_inc(v_fst_2069_);
v_snd_2070_ = lean_ctor_get(v_snd_2062_, 1);
lean_inc(v_snd_2070_);
lean_dec(v_snd_2062_);
v___x_2071_ = l_Lean_trace_profiler;
v___x_2072_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2049_, v___x_2071_);
if (v___x_2072_ == 0)
{
v___y_2090_ = v___x_2072_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2128_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2049_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; double v___x_2131_; double v___x_2132_; double v___x_2133_; 
v___x_2129_ = l_Lean_trace_profiler_threshold;
v___x_2130_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2049_, v___x_2129_);
v___x_2131_ = lean_float_of_nat(v___x_2130_);
v___x_2132_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_2133_ = lean_float_div(v___x_2131_, v___x_2132_);
v___y_2122_ = v___x_2133_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; double v___x_2136_; 
v___x_2134_ = l_Lean_trace_profiler_threshold;
v___x_2135_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2049_, v___x_2134_);
v___x_2136_ = lean_float_of_nat(v___x_2135_);
v___y_2122_ = v___x_2136_;
goto v___jp_2121_;
}
}
v___jp_2063_:
{
lean_object* v___x_2067_; 
lean_inc(v___y_2065_);
v___x_2067_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2051_, v_data_2066_, v___y_2065_, v___y_2064_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2068_; 
lean_dec_ref_known(v___x_2067_, 1);
v___x_2068_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2061_);
return v___x_2068_;
}
else
{
lean_dec(v_fst_2061_);
return v___x_2067_;
}
}
v___jp_2073_:
{
uint8_t v_result_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; double v___x_2079_; lean_object* v_data_2080_; 
v_result_2076_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_fst_2061_);
v___x_2077_ = lean_box(v_result_2076_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
v___x_2079_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2048_);
lean_inc_ref(v___x_2078_);
lean_inc(v_cls_2046_);
v_data_2080_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2080_, 0, v_cls_2046_);
lean_ctor_set(v_data_2080_, 1, v___x_2078_);
lean_ctor_set(v_data_2080_, 2, v_tag_2048_);
lean_ctor_set_float(v_data_2080_, sizeof(void*)*3, v___x_2079_);
lean_ctor_set_float(v_data_2080_, sizeof(void*)*3 + 8, v___x_2079_);
lean_ctor_set_uint8(v_data_2080_, sizeof(void*)*3 + 16, v_collapsed_2047_);
if (v___x_2072_ == 0)
{
lean_dec_ref_known(v___x_2078_, 1);
lean_dec(v_snd_2070_);
lean_dec(v_fst_2069_);
lean_dec_ref(v_tag_2048_);
lean_dec(v_cls_2046_);
v___y_2064_ = v_a_2075_;
v___y_2065_ = v___y_2074_;
v_data_2066_ = v_data_2080_;
goto v___jp_2063_;
}
else
{
lean_object* v_data_2081_; double v___x_2082_; double v___x_2083_; 
lean_dec_ref_known(v_data_2080_, 3);
v_data_2081_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2081_, 0, v_cls_2046_);
lean_ctor_set(v_data_2081_, 1, v___x_2078_);
lean_ctor_set(v_data_2081_, 2, v_tag_2048_);
v___x_2082_ = lean_unbox_float(v_fst_2069_);
lean_dec(v_fst_2069_);
lean_ctor_set_float(v_data_2081_, sizeof(void*)*3, v___x_2082_);
v___x_2083_ = lean_unbox_float(v_snd_2070_);
lean_dec(v_snd_2070_);
lean_ctor_set_float(v_data_2081_, sizeof(void*)*3 + 8, v___x_2083_);
lean_ctor_set_uint8(v_data_2081_, sizeof(void*)*3 + 16, v_collapsed_2047_);
v___y_2064_ = v_a_2075_;
v___y_2065_ = v___y_2074_;
v_data_2066_ = v_data_2081_;
goto v___jp_2063_;
}
}
v___jp_2084_:
{
lean_object* v_ref_2085_; lean_object* v___x_2086_; 
v_ref_2085_ = lean_ctor_get(v___y_2058_, 2);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
lean_inc(v___y_2055_);
lean_inc_ref(v___y_2054_);
lean_inc(v_fst_2061_);
v___x_2086_ = lean_apply_8(v_msg_2052_, v_fst_2061_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, lean_box(0));
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___y_2074_ = v_ref_2085_;
v_a_2075_ = v_a_2087_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_2074_ = v_ref_2085_;
v_a_2075_ = v___x_2088_;
goto v___jp_2073_;
}
}
v___jp_2089_:
{
if (v_clsEnabled_2050_ == 0)
{
if (v___y_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v_traceState_2092_; lean_object* v_env_2093_; lean_object* v_nextMacroScope_2094_; lean_object* v_ngen_2095_; lean_object* v_auxDeclNGen_2096_; lean_object* v_cache_2097_; lean_object* v_recordedDeps_2098_; lean_object* v_messages_2099_; lean_object* v_infoState_2100_; lean_object* v_snapshotTasks_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_snd_2070_);
lean_dec(v_fst_2069_);
lean_dec_ref(v_msg_2052_);
lean_dec_ref(v_tag_2048_);
lean_dec(v_cls_2046_);
v___x_2091_ = lean_st_ref_take(v___y_2059_);
v_traceState_2092_ = lean_ctor_get(v___x_2091_, 4);
v_env_2093_ = lean_ctor_get(v___x_2091_, 0);
v_nextMacroScope_2094_ = lean_ctor_get(v___x_2091_, 1);
v_ngen_2095_ = lean_ctor_get(v___x_2091_, 2);
v_auxDeclNGen_2096_ = lean_ctor_get(v___x_2091_, 3);
v_cache_2097_ = lean_ctor_get(v___x_2091_, 5);
v_recordedDeps_2098_ = lean_ctor_get(v___x_2091_, 6);
v_messages_2099_ = lean_ctor_get(v___x_2091_, 7);
v_infoState_2100_ = lean_ctor_get(v___x_2091_, 8);
v_snapshotTasks_2101_ = lean_ctor_get(v___x_2091_, 9);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2103_ = v___x_2091_;
v_isShared_2104_ = v_isSharedCheck_2120_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_snapshotTasks_2101_);
lean_inc(v_infoState_2100_);
lean_inc(v_messages_2099_);
lean_inc(v_recordedDeps_2098_);
lean_inc(v_cache_2097_);
lean_inc(v_traceState_2092_);
lean_inc(v_auxDeclNGen_2096_);
lean_inc(v_ngen_2095_);
lean_inc(v_nextMacroScope_2094_);
lean_inc(v_env_2093_);
lean_dec(v___x_2091_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2120_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
uint64_t v_tid_2105_; lean_object* v_traces_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2119_; 
v_tid_2105_ = lean_ctor_get_uint64(v_traceState_2092_, sizeof(void*)*1);
v_traces_2106_ = lean_ctor_get(v_traceState_2092_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_traceState_2092_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2108_ = v_traceState_2092_;
v_isShared_2109_ = v_isSharedCheck_2119_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_traces_2106_);
lean_dec(v_traceState_2092_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2119_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2051_, v_traces_2106_);
lean_dec_ref(v_traces_2106_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2110_);
v___x_2112_ = v___x_2108_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2110_);
lean_ctor_set_uint64(v_reuseFailAlloc_2118_, sizeof(void*)*1, v_tid_2105_);
v___x_2112_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v___x_2112_);
v___x_2114_ = v___x_2103_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_env_2093_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_nextMacroScope_2094_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_ngen_2095_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_auxDeclNGen_2096_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2117_, 5, v_cache_2097_);
lean_ctor_set(v_reuseFailAlloc_2117_, 6, v_recordedDeps_2098_);
lean_ctor_set(v_reuseFailAlloc_2117_, 7, v_messages_2099_);
lean_ctor_set(v_reuseFailAlloc_2117_, 8, v_infoState_2100_);
lean_ctor_set(v_reuseFailAlloc_2117_, 9, v_snapshotTasks_2101_);
v___x_2114_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_st_ref_put(v___y_2059_, v___x_2114_);
v___x_2116_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2061_);
return v___x_2116_;
}
}
}
}
}
else
{
goto v___jp_2084_;
}
}
else
{
goto v___jp_2084_;
}
}
v___jp_2121_:
{
double v___x_2123_; double v___x_2124_; double v___x_2125_; uint8_t v___x_2126_; 
v___x_2123_ = lean_unbox_float(v_snd_2070_);
v___x_2124_ = lean_unbox_float(v_fst_2069_);
v___x_2125_ = lean_float_sub(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_float_decLt(v___y_2122_, v___x_2125_);
v___y_2090_ = v___x_2126_;
goto v___jp_2089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object* v_cls_2137_, lean_object* v_collapsed_2138_, lean_object* v_tag_2139_, lean_object* v_opts_2140_, lean_object* v_clsEnabled_2141_, lean_object* v_oldTraces_2142_, lean_object* v_msg_2143_, lean_object* v_resStartStop_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
uint8_t v_collapsed_boxed_2152_; uint8_t v_clsEnabled_boxed_2153_; lean_object* v_res_2154_; 
v_collapsed_boxed_2152_ = lean_unbox(v_collapsed_2138_);
v_clsEnabled_boxed_2153_ = lean_unbox(v_clsEnabled_2141_);
v_res_2154_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_cls_2137_, v_collapsed_boxed_2152_, v_tag_2139_, v_opts_2140_, v_clsEnabled_boxed_2153_, v_oldTraces_2142_, v_msg_2143_, v_resStartStop_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec_ref(v_opts_2140_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
lean_object* v_ks_2159_; lean_object* v_vs_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2184_; 
v_ks_2159_ = lean_ctor_get(v_x_2155_, 0);
v_vs_2160_ = lean_ctor_get(v_x_2155_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_x_2155_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2162_ = v_x_2155_;
v_isShared_2163_ = v_isSharedCheck_2184_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_vs_2160_);
lean_inc(v_ks_2159_);
lean_dec(v_x_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2184_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_array_get_size(v_ks_2159_);
v___x_2165_ = lean_nat_dec_lt(v_x_2156_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec(v_x_2156_);
v___x_2166_ = lean_array_push(v_ks_2159_, v_x_2157_);
v___x_2167_ = lean_array_push(v_vs_2160_, v_x_2158_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v___x_2167_);
lean_ctor_set(v___x_2162_, 0, v___x_2166_);
v___x_2169_ = v___x_2162_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
else
{
lean_object* v_k_x27_2171_; uint8_t v___x_2172_; 
v_k_x27_2171_ = lean_array_fget_borrowed(v_ks_2159_, v_x_2156_);
v___x_2172_ = l_Lean_instBEqMVarId_beq(v_x_2157_, v_k_x27_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2174_; 
if (v_isShared_2163_ == 0)
{
v___x_2174_ = v___x_2162_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_ks_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_vs_2160_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_add(v_x_2156_, v___x_2175_);
lean_dec(v_x_2156_);
v_x_2155_ = v___x_2174_;
v_x_2156_ = v___x_2176_;
goto _start;
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2179_ = lean_array_fset(v_ks_2159_, v_x_2156_, v_x_2157_);
v___x_2180_ = lean_array_fset(v_vs_2160_, v_x_2156_, v_x_2158_);
lean_dec(v_x_2156_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v___x_2180_);
lean_ctor_set(v___x_2162_, 0, v___x_2179_);
v___x_2182_ = v___x_2162_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_n_2185_, lean_object* v_k_2186_, lean_object* v_v_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_n_2185_, v___x_2188_, v_k_2186_, v_v_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2191_, size_t v_x_2192_, size_t v_x_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
if (lean_obj_tag(v_x_2191_) == 0)
{
lean_object* v_es_2196_; size_t v___x_2197_; size_t v___x_2198_; lean_object* v_j_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_es_2196_ = lean_ctor_get(v_x_2191_, 0);
v___x_2197_ = ((size_t)31ULL);
v___x_2198_ = lean_usize_land(v_x_2192_, v___x_2197_);
v_j_2199_ = lean_usize_to_nat(v___x_2198_);
v___x_2200_ = lean_array_get_size(v_es_2196_);
v___x_2201_ = lean_nat_dec_lt(v_j_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_dec(v_j_2199_);
lean_dec(v_x_2195_);
lean_dec(v_x_2194_);
return v_x_2191_;
}
else
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2240_; 
lean_inc_ref(v_es_2196_);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_x_2191_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v_x_2191_, 0);
lean_dec(v_unused_2241_);
v___x_2203_ = v_x_2191_;
v_isShared_2204_ = v_isSharedCheck_2240_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v_x_2191_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2240_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v_v_2205_; lean_object* v___x_2206_; lean_object* v_xs_x27_2207_; lean_object* v___y_2209_; 
v_v_2205_ = lean_array_fget(v_es_2196_, v_j_2199_);
v___x_2206_ = lean_box(0);
v_xs_x27_2207_ = lean_array_fset(v_es_2196_, v_j_2199_, v___x_2206_);
switch(lean_obj_tag(v_v_2205_))
{
case 0:
{
lean_object* v_key_2214_; lean_object* v_val_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2225_; 
v_key_2214_ = lean_ctor_get(v_v_2205_, 0);
v_val_2215_ = lean_ctor_get(v_v_2205_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_v_2205_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2217_ = v_v_2205_;
v_isShared_2218_ = v_isSharedCheck_2225_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_val_2215_);
lean_inc(v_key_2214_);
lean_dec(v_v_2205_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2225_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
uint8_t v___x_2219_; 
v___x_2219_ = l_Lean_instBEqMVarId_beq(v_x_2194_, v_key_2214_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_del_object(v___x_2217_);
v___x_2220_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2214_, v_val_2215_, v_x_2194_, v_x_2195_);
v___x_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
v___y_2209_ = v___x_2221_;
goto v___jp_2208_;
}
else
{
lean_object* v___x_2223_; 
lean_dec(v_val_2215_);
lean_dec(v_key_2214_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_x_2195_);
lean_ctor_set(v___x_2217_, 0, v_x_2194_);
v___x_2223_ = v___x_2217_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_x_2194_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_x_2195_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
v___y_2209_ = v___x_2223_;
goto v___jp_2208_;
}
}
}
}
case 1:
{
lean_object* v_node_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2238_; 
v_node_2226_ = lean_ctor_get(v_v_2205_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_v_2205_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2228_ = v_v_2205_;
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_node_2226_);
lean_dec(v_v_2205_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
size_t v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2230_ = ((size_t)5ULL);
v___x_2231_ = lean_usize_shift_right(v_x_2192_, v___x_2230_);
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = lean_usize_add(v_x_2193_, v___x_2232_);
v___x_2234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_node_2226_, v___x_2231_, v___x_2233_, v_x_2194_, v_x_2195_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2234_);
v___x_2236_ = v___x_2228_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v___y_2209_ = v___x_2236_;
goto v___jp_2208_;
}
}
}
default: 
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_x_2194_);
lean_ctor_set(v___x_2239_, 1, v_x_2195_);
v___y_2209_ = v___x_2239_;
goto v___jp_2208_;
}
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_array_fset(v_xs_x27_2207_, v_j_2199_, v___y_2209_);
lean_dec(v_j_2199_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2210_);
v___x_2212_ = v___x_2203_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
else
{
lean_object* v_ks_2242_; lean_object* v_vs_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2261_; 
v_ks_2242_ = lean_ctor_get(v_x_2191_, 0);
v_vs_2243_ = lean_ctor_get(v_x_2191_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_x_2191_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2245_ = v_x_2191_;
v_isShared_2246_ = v_isSharedCheck_2261_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_vs_2243_);
lean_inc(v_ks_2242_);
lean_dec(v_x_2191_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2261_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_ks_2242_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_vs_2243_);
v___x_2248_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v_newNode_2249_; size_t v___x_2250_; uint8_t v___x_2251_; 
v_newNode_2249_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v___x_2248_, v_x_2194_, v_x_2195_);
v___x_2250_ = ((size_t)7ULL);
v___x_2251_ = lean_usize_dec_le(v___x_2250_, v_x_2193_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2252_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2249_);
v___x_2253_ = lean_unsigned_to_nat(4u);
v___x_2254_ = lean_nat_dec_lt(v___x_2252_, v___x_2253_);
lean_dec(v___x_2252_);
if (v___x_2254_ == 0)
{
lean_object* v_ks_2255_; lean_object* v_vs_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_ks_2255_ = lean_ctor_get(v_newNode_2249_, 0);
lean_inc_ref(v_ks_2255_);
v_vs_2256_ = lean_ctor_get(v_newNode_2249_, 1);
lean_inc_ref(v_vs_2256_);
lean_dec_ref(v_newNode_2249_);
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_2259_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_x_2193_, v_ks_2255_, v_vs_2256_, v___x_2257_, v___x_2258_);
lean_dec_ref(v_vs_2256_);
lean_dec_ref(v_ks_2255_);
return v___x_2259_;
}
else
{
return v_newNode_2249_;
}
}
else
{
return v_newNode_2249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t v_depth_2262_, lean_object* v_keys_2263_, lean_object* v_vals_2264_, lean_object* v_i_2265_, lean_object* v_entries_2266_){
_start:
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_array_get_size(v_keys_2263_);
v___x_2268_ = lean_nat_dec_lt(v_i_2265_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_dec(v_i_2265_);
return v_entries_2266_;
}
else
{
lean_object* v_k_2269_; lean_object* v_v_2270_; uint64_t v___x_2271_; size_t v_h_2272_; size_t v___x_2273_; lean_object* v___x_2274_; size_t v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; size_t v_h_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_k_2269_ = lean_array_fget_borrowed(v_keys_2263_, v_i_2265_);
v_v_2270_ = lean_array_fget_borrowed(v_vals_2264_, v_i_2265_);
v___x_2271_ = l_Lean_instHashableMVarId_hash(v_k_2269_);
v_h_2272_ = lean_uint64_to_usize(v___x_2271_);
v___x_2273_ = ((size_t)5ULL);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = ((size_t)1ULL);
v___x_2276_ = lean_usize_sub(v_depth_2262_, v___x_2275_);
v___x_2277_ = lean_usize_mul(v___x_2273_, v___x_2276_);
v_h_2278_ = lean_usize_shift_right(v_h_2272_, v___x_2277_);
v___x_2279_ = lean_nat_add(v_i_2265_, v___x_2274_);
lean_dec(v_i_2265_);
lean_inc(v_v_2270_);
lean_inc(v_k_2269_);
v___x_2280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_entries_2266_, v_h_2278_, v_depth_2262_, v_k_2269_, v_v_2270_);
v_i_2265_ = v___x_2279_;
v_entries_2266_ = v___x_2280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_depth_2282_, lean_object* v_keys_2283_, lean_object* v_vals_2284_, lean_object* v_i_2285_, lean_object* v_entries_2286_){
_start:
{
size_t v_depth_boxed_2287_; lean_object* v_res_2288_; 
v_depth_boxed_2287_ = lean_unbox_usize(v_depth_2282_);
lean_dec(v_depth_2282_);
v_res_2288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_boxed_2287_, v_keys_2283_, v_vals_2284_, v_i_2285_, v_entries_2286_);
lean_dec_ref(v_vals_2284_);
lean_dec_ref(v_keys_2283_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_){
_start:
{
size_t v_x_17278__boxed_2294_; size_t v_x_17279__boxed_2295_; lean_object* v_res_2296_; 
v_x_17278__boxed_2294_ = lean_unbox_usize(v_x_2290_);
lean_dec(v_x_2290_);
v_x_17279__boxed_2295_ = lean_unbox_usize(v_x_2291_);
lean_dec(v_x_2291_);
v_res_2296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2289_, v_x_17278__boxed_2294_, v_x_17279__boxed_2295_, v_x_2292_, v_x_2293_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object* v_x_2297_, lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
uint64_t v___x_2300_; size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = l_Lean_instHashableMVarId_hash(v_x_2298_);
v___x_2301_ = lean_uint64_to_usize(v___x_2300_);
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2297_, v___x_2301_, v___x_2302_, v_x_2298_, v_x_2299_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v_mvarId_2304_, lean_object* v_val_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v_mctx_2309_; lean_object* v_cache_2310_; lean_object* v_zetaDeltaFVarIds_2311_; lean_object* v_postponed_2312_; lean_object* v_diag_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2342_; 
v___x_2308_ = lean_st_ref_take(v___y_2306_);
v_mctx_2309_ = lean_ctor_get(v___x_2308_, 0);
v_cache_2310_ = lean_ctor_get(v___x_2308_, 1);
v_zetaDeltaFVarIds_2311_ = lean_ctor_get(v___x_2308_, 2);
v_postponed_2312_ = lean_ctor_get(v___x_2308_, 3);
v_diag_2313_ = lean_ctor_get(v___x_2308_, 4);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2315_ = v___x_2308_;
v_isShared_2316_ = v_isSharedCheck_2342_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_diag_2313_);
lean_inc(v_postponed_2312_);
lean_inc(v_zetaDeltaFVarIds_2311_);
lean_inc(v_cache_2310_);
lean_inc(v_mctx_2309_);
lean_dec(v___x_2308_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2342_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_depth_2317_; lean_object* v_levelAssignDepth_2318_; lean_object* v_lmvarCounter_2319_; lean_object* v_mvarCounter_2320_; lean_object* v_lDecls_2321_; lean_object* v_decls_2322_; lean_object* v_userNames_2323_; lean_object* v_lAssignment_2324_; lean_object* v_eAssignment_2325_; lean_object* v_dAssignment_2326_; lean_object* v_synthNormMemo_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2341_; 
v_depth_2317_ = lean_ctor_get(v_mctx_2309_, 0);
v_levelAssignDepth_2318_ = lean_ctor_get(v_mctx_2309_, 1);
v_lmvarCounter_2319_ = lean_ctor_get(v_mctx_2309_, 2);
v_mvarCounter_2320_ = lean_ctor_get(v_mctx_2309_, 3);
v_lDecls_2321_ = lean_ctor_get(v_mctx_2309_, 4);
v_decls_2322_ = lean_ctor_get(v_mctx_2309_, 5);
v_userNames_2323_ = lean_ctor_get(v_mctx_2309_, 6);
v_lAssignment_2324_ = lean_ctor_get(v_mctx_2309_, 7);
v_eAssignment_2325_ = lean_ctor_get(v_mctx_2309_, 8);
v_dAssignment_2326_ = lean_ctor_get(v_mctx_2309_, 9);
v_synthNormMemo_2327_ = lean_ctor_get(v_mctx_2309_, 10);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_mctx_2309_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2329_ = v_mctx_2309_;
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_synthNormMemo_2327_);
lean_inc(v_dAssignment_2326_);
lean_inc(v_eAssignment_2325_);
lean_inc(v_lAssignment_2324_);
lean_inc(v_userNames_2323_);
lean_inc(v_decls_2322_);
lean_inc(v_lDecls_2321_);
lean_inc(v_mvarCounter_2320_);
lean_inc(v_lmvarCounter_2319_);
lean_inc(v_levelAssignDepth_2318_);
lean_inc(v_depth_2317_);
lean_dec(v_mctx_2309_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2331_ = lean_box(0);
v___x_2332_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_eAssignment_2325_, v_mvarId_2304_, v_val_2305_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 8, v___x_2332_);
v___x_2334_ = v___x_2329_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_depth_2317_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_levelAssignDepth_2318_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_lmvarCounter_2319_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_mvarCounter_2320_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v_lDecls_2321_);
lean_ctor_set(v_reuseFailAlloc_2340_, 5, v_decls_2322_);
lean_ctor_set(v_reuseFailAlloc_2340_, 6, v_userNames_2323_);
lean_ctor_set(v_reuseFailAlloc_2340_, 7, v_lAssignment_2324_);
lean_ctor_set(v_reuseFailAlloc_2340_, 8, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2340_, 9, v_dAssignment_2326_);
lean_ctor_set(v_reuseFailAlloc_2340_, 10, v_synthNormMemo_2327_);
v___x_2334_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2334_);
v___x_2336_ = v___x_2315_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_cache_2310_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_zetaDeltaFVarIds_2311_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_postponed_2312_);
lean_ctor_set(v_reuseFailAlloc_2339_, 4, v_diag_2313_);
v___x_2336_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_st_ref_put(v___y_2306_, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2331_);
return v___x_2338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object* v_mvarId_2343_, lean_object* v_val_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2343_, v_val_2344_, v___y_2345_);
lean_dec(v___y_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_keys_2348_, lean_object* v_i_2349_, lean_object* v_k_2350_){
_start:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = lean_array_get_size(v_keys_2348_);
v___x_2352_ = lean_nat_dec_lt(v_i_2349_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec(v_i_2349_);
return v___x_2352_;
}
else
{
lean_object* v_k_x27_2353_; uint8_t v___x_2354_; 
v_k_x27_2353_ = lean_array_fget_borrowed(v_keys_2348_, v_i_2349_);
v___x_2354_ = l_Lean_instBEqMVarId_beq(v_k_2350_, v_k_x27_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = lean_nat_add(v_i_2349_, v___x_2355_);
lean_dec(v_i_2349_);
v_i_2349_ = v___x_2356_;
goto _start;
}
else
{
lean_dec(v_i_2349_);
return v___x_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_keys_2358_, lean_object* v_i_2359_, lean_object* v_k_2360_){
_start:
{
uint8_t v_res_2361_; lean_object* v_r_2362_; 
v_res_2361_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2358_, v_i_2359_, v_k_2360_);
lean_dec(v_k_2360_);
lean_dec_ref(v_keys_2358_);
v_r_2362_ = lean_box(v_res_2361_);
return v_r_2362_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(lean_object* v_x_2363_, size_t v_x_2364_, lean_object* v_x_2365_){
_start:
{
if (lean_obj_tag(v_x_2363_) == 0)
{
lean_object* v_es_2366_; lean_object* v___x_2367_; size_t v___x_2368_; size_t v___x_2369_; lean_object* v_j_2370_; lean_object* v___x_2371_; 
v_es_2366_ = lean_ctor_get(v_x_2363_, 0);
v___x_2367_ = lean_box(2);
v___x_2368_ = ((size_t)31ULL);
v___x_2369_ = lean_usize_land(v_x_2364_, v___x_2368_);
v_j_2370_ = lean_usize_to_nat(v___x_2369_);
v___x_2371_ = lean_array_get_borrowed(v___x_2367_, v_es_2366_, v_j_2370_);
lean_dec(v_j_2370_);
switch(lean_obj_tag(v___x_2371_))
{
case 0:
{
lean_object* v_key_2372_; uint8_t v___x_2373_; 
v_key_2372_ = lean_ctor_get(v___x_2371_, 0);
v___x_2373_ = l_Lean_instBEqMVarId_beq(v_x_2365_, v_key_2372_);
return v___x_2373_;
}
case 1:
{
lean_object* v_node_2374_; size_t v___x_2375_; size_t v___x_2376_; 
v_node_2374_ = lean_ctor_get(v___x_2371_, 0);
v___x_2375_ = ((size_t)5ULL);
v___x_2376_ = lean_usize_shift_right(v_x_2364_, v___x_2375_);
v_x_2363_ = v_node_2374_;
v_x_2364_ = v___x_2376_;
goto _start;
}
default: 
{
uint8_t v___x_2378_; 
v___x_2378_ = 0;
return v___x_2378_;
}
}
}
else
{
lean_object* v_ks_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_ks_2379_ = lean_ctor_get(v_x_2363_, 0);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_ks_2379_, v___x_2380_, v_x_2365_);
return v___x_2381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
size_t v_x_17500__boxed_2385_; uint8_t v_res_2386_; lean_object* v_r_2387_; 
v_x_17500__boxed_2385_ = lean_unbox_usize(v_x_2383_);
lean_dec(v_x_2383_);
v_res_2386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2382_, v_x_17500__boxed_2385_, v_x_2384_);
lean_dec(v_x_2384_);
lean_dec_ref(v_x_2382_);
v_r_2387_ = lean_box(v_res_2386_);
return v_r_2387_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(lean_object* v_x_2388_, lean_object* v_x_2389_){
_start:
{
uint64_t v___x_2390_; size_t v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = l_Lean_instHashableMVarId_hash(v_x_2389_);
v___x_2391_ = lean_uint64_to_usize(v___x_2390_);
v___x_2392_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2388_, v___x_2391_, v_x_2389_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg___boxed(lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
uint8_t v_res_2395_; lean_object* v_r_2396_; 
v_res_2395_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2393_, v_x_2394_);
lean_dec(v_x_2394_);
lean_dec_ref(v_x_2393_);
v_r_2396_ = lean_box(v_res_2395_);
return v_r_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(lean_object* v_mvarId_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v_mctx_2401_; lean_object* v_eAssignment_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2400_ = lean_st_ref_get(v___y_2398_);
v_mctx_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc_ref(v_mctx_2401_);
lean_dec(v___x_2400_);
v_eAssignment_2402_ = lean_ctor_get(v_mctx_2401_, 8);
lean_inc_ref(v_eAssignment_2402_);
lean_dec_ref(v_mctx_2401_);
v___x_2403_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_eAssignment_2402_, v_mvarId_2397_);
lean_dec_ref(v_eAssignment_2402_);
v___x_2404_ = lean_box(v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg___boxed(lean_object* v_mvarId_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec(v_mvarId_2406_);
return v_res_2409_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2410_; double v___x_2411_; 
v___x_2410_ = lean_unsigned_to_nat(1000000000u);
v___x_2411_ = lean_float_of_nat(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1));
v___x_2414_ = l_Lean_stringToMessageData(v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(lean_object* v___x_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v___x_2415_, v___y_2419_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2589_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2589_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2589_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_unbox(v_a_2424_);
lean_dec(v_a_2424_);
if (v___x_2428_ == 0)
{
uint8_t v___x_2429_; lean_object* v___x_2430_; 
lean_del_object(v___x_2426_);
v___x_2429_ = 1;
lean_inc(v___x_2415_);
v___x_2430_ = l_Lean_MVarId_getType(v___x_2415_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_toCold_2431_; lean_object* v_options_2432_; uint8_t v_hasTrace_2433_; 
v_toCold_2431_ = lean_ctor_get(v___y_2420_, 0);
v_options_2432_ = lean_ctor_get(v_toCold_2431_, 2);
v_hasTrace_2433_ = lean_ctor_get_uint8(v_options_2432_, sizeof(void*)*1);
if (v_hasTrace_2433_ == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2435_ = l_Lean_Meta_mkDefault(v_a_2434_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2415_, v_a_2436_, v___y_2419_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2445_; 
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; 
v_unused_2446_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2446_);
v___x_2439_ = v___x_2437_;
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2437_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = lean_box(0);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
else
{
return v___x_2437_;
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v___x_2415_);
v_a_2447_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2435_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2435_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v_inheritedTraceOptions_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_a_2465_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v_a_2480_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v_a_2485_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v_a_2490_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v_a_2502_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v_a_2507_; 
v_a_2455_ = lean_ctor_get(v___x_2430_, 0);
lean_inc_n(v_a_2455_, 2);
lean_dec_ref_known(v___x_2430_, 1);
v_inheritedTraceOptions_2456_ = lean_ctor_get(v_toCold_2431_, 11);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2457_, 0, v_a_2455_);
v___x_2458_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2459_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_2460_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2456_, v_options_2432_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = l_Lean_trace_profiler;
v___x_2551_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2432_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_dec_ref(v___f_2457_);
v___x_2552_ = l_Lean_Meta_mkDefault(v_a_2455_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_n(v_a_2553_, 2);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2415_, v_a_2553_, v___y_2419_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2567_; 
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v___x_2554_, 0);
lean_dec(v_unused_2568_);
v___x_2556_ = v___x_2554_;
v_isShared_2557_ = v_isSharedCheck_2567_;
goto v_resetjp_2555_;
}
else
{
lean_dec(v___x_2554_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2567_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
if (v___x_2461_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_dec(v_a_2553_);
v___x_2558_ = lean_box(0);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2558_);
v___x_2560_ = v___x_2556_;
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
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_del_object(v___x_2556_);
v___x_2562_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2563_ = lean_unsigned_to_nat(30u);
v___x_2564_ = l_Lean_inlineExprTrailing(v_a_2553_, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2562_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2458_, v___x_2565_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2566_;
}
}
}
else
{
lean_dec(v_a_2553_);
return v___x_2554_;
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v___x_2415_);
v_a_2569_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2552_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2552_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
goto v___jp_2509_;
}
}
else
{
goto v___jp_2509_;
}
v___jp_2462_:
{
lean_object* v___x_2466_; double v___x_2467_; double v___x_2468_; double v___x_2469_; double v___x_2470_; double v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2466_ = lean_io_mono_nanos_now();
v___x_2467_ = lean_float_of_nat(v___y_2464_);
v___x_2468_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_2469_ = lean_float_div(v___x_2467_, v___x_2468_);
v___x_2470_ = lean_float_of_nat(v___x_2466_);
v___x_2471_ = lean_float_div(v___x_2470_, v___x_2468_);
v___x_2472_ = lean_box_float(v___x_2469_);
v___x_2473_ = lean_box_float(v___x_2471_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2465_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2458_, v___x_2429_, v___x_2459_, v_options_2432_, v___x_2461_, v___y_2463_, v___f_2457_, v___x_2475_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2476_;
}
v___jp_2477_:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_a_2480_);
v___y_2463_ = v___y_2478_;
v___y_2464_ = v___y_2479_;
v_a_2465_ = v___x_2481_;
goto v___jp_2462_;
}
v___jp_2482_:
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_a_2485_);
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2484_;
v_a_2465_ = v___x_2486_;
goto v___jp_2462_;
}
v___jp_2487_:
{
lean_object* v___x_2491_; double v___x_2492_; double v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2491_ = lean_io_get_num_heartbeats();
v___x_2492_ = lean_float_of_nat(v___y_2489_);
v___x_2493_ = lean_float_of_nat(v___x_2491_);
v___x_2494_ = lean_box_float(v___x_2492_);
v___x_2495_ = lean_box_float(v___x_2493_);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v_a_2490_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2458_, v___x_2429_, v___x_2459_, v_options_2432_, v___x_2461_, v___y_2488_, v___f_2457_, v___x_2497_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2498_;
}
v___jp_2499_:
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2502_);
v___y_2488_ = v___y_2500_;
v___y_2489_ = v___y_2501_;
v_a_2490_ = v___x_2503_;
goto v___jp_2487_;
}
v___jp_2504_:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2507_);
v___y_2488_ = v___y_2505_;
v___y_2489_ = v___y_2506_;
v_a_2490_ = v___x_2508_;
goto v___jp_2487_;
}
v___jp_2509_:
{
lean_object* v___x_2510_; 
v___x_2510_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_2421_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v___x_2512_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2513_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2432_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_io_mono_nanos_now();
v___x_2515_ = l_Lean_Meta_mkDefault(v_a_2455_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_n(v_a_2516_, 2);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2415_, v_a_2516_, v___y_2419_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
if (v___x_2461_ == 0)
{
lean_object* v___x_2518_; 
lean_dec(v_a_2516_);
v___x_2518_ = lean_box(0);
v___y_2483_ = v_a_2511_;
v___y_2484_ = v___x_2514_;
v_a_2485_ = v___x_2518_;
goto v___jp_2482_;
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2520_ = lean_unsigned_to_nat(30u);
v___x_2521_ = l_Lean_inlineExprTrailing(v_a_2516_, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2519_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2458_, v___x_2522_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___y_2483_ = v_a_2511_;
v___y_2484_ = v___x_2514_;
v_a_2485_ = v_a_2524_;
goto v___jp_2482_;
}
else
{
lean_object* v_a_2525_; 
v_a_2525_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2523_, 1);
v___y_2478_ = v_a_2511_;
v___y_2479_ = v___x_2514_;
v_a_2480_ = v_a_2525_;
goto v___jp_2477_;
}
}
}
else
{
lean_object* v_a_2526_; 
lean_dec(v_a_2516_);
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2517_, 1);
v___y_2478_ = v_a_2511_;
v___y_2479_ = v___x_2514_;
v_a_2480_ = v_a_2526_;
goto v___jp_2477_;
}
}
else
{
lean_object* v_a_2527_; 
lean_dec(v___x_2415_);
v_a_2527_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2515_, 1);
v___y_2478_ = v_a_2511_;
v___y_2479_ = v___x_2514_;
v_a_2480_ = v_a_2527_;
goto v___jp_2477_;
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_io_get_num_heartbeats();
v___x_2529_ = l_Lean_Meta_mkDefault(v_a_2455_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_n(v_a_2530_, 2);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2415_, v_a_2530_, v___y_2419_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_dec_ref_known(v___x_2531_, 1);
if (v___x_2461_ == 0)
{
lean_object* v___x_2532_; 
lean_dec(v_a_2530_);
v___x_2532_ = lean_box(0);
v___y_2505_ = v_a_2511_;
v___y_2506_ = v___x_2528_;
v_a_2507_ = v___x_2532_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2534_ = lean_unsigned_to_nat(30u);
v___x_2535_ = l_Lean_inlineExprTrailing(v_a_2530_, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2533_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2458_, v___x_2536_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v___y_2505_ = v_a_2511_;
v___y_2506_ = v___x_2528_;
v_a_2507_ = v_a_2538_;
goto v___jp_2504_;
}
else
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2537_, 1);
v___y_2500_ = v_a_2511_;
v___y_2501_ = v___x_2528_;
v_a_2502_ = v_a_2539_;
goto v___jp_2499_;
}
}
}
else
{
lean_object* v_a_2540_; 
lean_dec(v_a_2530_);
v_a_2540_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2531_, 1);
v___y_2500_ = v_a_2511_;
v___y_2501_ = v___x_2528_;
v_a_2502_ = v_a_2540_;
goto v___jp_2499_;
}
}
else
{
lean_object* v_a_2541_; 
lean_dec(v___x_2415_);
v_a_2541_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2529_, 1);
v___y_2500_ = v_a_2511_;
v___y_2501_ = v___x_2528_;
v_a_2502_ = v_a_2541_;
goto v___jp_2499_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v___f_2457_);
lean_dec(v_a_2455_);
lean_dec(v___x_2415_);
v_a_2542_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2510_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2510_);
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
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___x_2415_);
v_a_2577_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2430_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2430_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec(v___x_2415_);
v___x_2585_ = lean_box(0);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2585_);
v___x_2587_ = v___x_2426_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
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
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___x_2415_);
v_a_2590_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2423_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2423_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2607_, size_t v_i_2608_, size_t v_stop_2609_, lean_object* v_b_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_usize_dec_eq(v_i_2608_, v_stop_2609_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; 
v___x_2619_ = lean_array_uget_borrowed(v_as_2607_, v_i_2608_);
lean_inc_n(v___x_2619_, 2);
v___f_2620_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2620_, 0, v___x_2619_);
v___x_2621_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2619_, v___f_2620_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; size_t v___x_2623_; size_t v___x_2624_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = ((size_t)1ULL);
v___x_2624_ = lean_usize_add(v_i_2608_, v___x_2623_);
v_i_2608_ = v___x_2624_;
v_b_2610_ = v_a_2622_;
goto _start;
}
else
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_b_2610_);
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2627_, lean_object* v_i_2628_, lean_object* v_stop_2629_, lean_object* v_b_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
size_t v_i_boxed_2638_; size_t v_stop_boxed_2639_; lean_object* v_res_2640_; 
v_i_boxed_2638_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_stop_boxed_2639_ = lean_unbox_usize(v_stop_2629_);
lean_dec(v_stop_2629_);
v_res_2640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2627_, v_i_boxed_2638_, v_stop_boxed_2639_, v_b_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec_ref(v_as_2627_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2641_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2664_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_array_get_size(v_a_2650_);
v___x_2656_ = lean_box(0);
v___x_2657_ = lean_nat_dec_lt(v___x_2654_, v___x_2655_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2659_; 
lean_dec(v_a_2650_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2656_);
v___x_2659_ = v___x_2652_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2656_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
else
{
size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; 
lean_del_object(v___x_2652_);
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = lean_usize_of_nat(v___x_2655_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2650_, v___x_2661_, v___x_2662_, v___x_2656_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2650_);
return v___x_2663_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
v_a_2665_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2649_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2649_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2682_, v___y_2686_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v_mvarId_2691_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v_mvarId_2700_, lean_object* v_val_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2700_, v_val_2701_, v___y_2705_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v_mvarId_2710_, lean_object* v_val_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2710_, v_val_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object* v_00_u03b1_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_2721_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(v_00_u03b1_2730_, v_x_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2739_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2740_, lean_object* v_x_2741_, lean_object* v_x_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2741_, v_x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
uint8_t v_res_2747_; lean_object* v_r_2748_; 
v_res_2747_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2744_, v_x_2745_, v_x_2746_);
lean_dec(v_x_2746_);
lean_dec_ref(v_x_2745_);
v_r_2748_ = lean_box(v_res_2747_);
return v_r_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object* v_00_u03b2_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_x_2750_, v_x_2751_, v_x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object* v_oldTraces_2754_, lean_object* v_data_2755_, lean_object* v_ref_2756_, lean_object* v_msg_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2754_, v_data_2755_, v_ref_2756_, v_msg_2757_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object* v_oldTraces_2766_, lean_object* v_data_2767_, lean_object* v_ref_2768_, lean_object* v_msg_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_oldTraces_2766_, v_data_2767_, v_ref_2768_, v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2777_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2778_, lean_object* v_x_2779_, size_t v_x_2780_, lean_object* v_x_2781_){
_start:
{
uint8_t v___x_2782_; 
v___x_2782_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2779_, v_x_2780_, v_x_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_){
_start:
{
size_t v_x_18173__boxed_2787_; uint8_t v_res_2788_; lean_object* v_r_2789_; 
v_x_18173__boxed_2787_ = lean_unbox_usize(v_x_2785_);
lean_dec(v_x_2785_);
v_res_2788_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2783_, v_x_2784_, v_x_18173__boxed_2787_, v_x_2786_);
lean_dec(v_x_2786_);
lean_dec_ref(v_x_2784_);
v_r_2789_ = lean_box(v_res_2788_);
return v_r_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2790_, lean_object* v_x_2791_, size_t v_x_2792_, size_t v_x_2793_, lean_object* v_x_2794_, lean_object* v_x_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2791_, v_x_2792_, v_x_2793_, v_x_2794_, v_x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_){
_start:
{
size_t v_x_18184__boxed_2803_; size_t v_x_18185__boxed_2804_; lean_object* v_res_2805_; 
v_x_18184__boxed_2803_ = lean_unbox_usize(v_x_2799_);
lean_dec(v_x_2799_);
v_x_18185__boxed_2804_ = lean_unbox_usize(v_x_2800_);
lean_dec(v_x_2800_);
v_res_2805_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(v_00_u03b2_2797_, v_x_2798_, v_x_18184__boxed_2803_, v_x_18185__boxed_2804_, v_x_2801_, v_x_2802_);
return v_res_2805_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2806_, lean_object* v_keys_2807_, lean_object* v_vals_2808_, lean_object* v_heq_2809_, lean_object* v_i_2810_, lean_object* v_k_2811_){
_start:
{
uint8_t v___x_2812_; 
v___x_2812_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2807_, v_i_2810_, v_k_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2813_, lean_object* v_keys_2814_, lean_object* v_vals_2815_, lean_object* v_heq_2816_, lean_object* v_i_2817_, lean_object* v_k_2818_){
_start:
{
uint8_t v_res_2819_; lean_object* v_r_2820_; 
v_res_2819_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2813_, v_keys_2814_, v_vals_2815_, v_heq_2816_, v_i_2817_, v_k_2818_);
lean_dec(v_k_2818_);
lean_dec_ref(v_vals_2815_);
lean_dec_ref(v_keys_2814_);
v_r_2820_ = lean_box(v_res_2819_);
return v_r_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_2821_, lean_object* v_n_2822_, lean_object* v_k_2823_, lean_object* v_v_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v_n_2822_, v_k_2823_, v_v_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b2_2826_, size_t v_depth_2827_, lean_object* v_keys_2828_, lean_object* v_vals_2829_, lean_object* v_heq_2830_, lean_object* v_i_2831_, lean_object* v_entries_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2827_, v_keys_2828_, v_vals_2829_, v_i_2831_, v_entries_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b2_2834_, lean_object* v_depth_2835_, lean_object* v_keys_2836_, lean_object* v_vals_2837_, lean_object* v_heq_2838_, lean_object* v_i_2839_, lean_object* v_entries_2840_){
_start:
{
size_t v_depth_boxed_2841_; lean_object* v_res_2842_; 
v_depth_boxed_2841_ = lean_unbox_usize(v_depth_2835_);
lean_dec(v_depth_2835_);
v_res_2842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(v_00_u03b2_2834_, v_depth_boxed_2841_, v_keys_2836_, v_vals_2837_, v_heq_2838_, v_i_2839_, v_entries_2840_);
lean_dec_ref(v_vals_2837_);
lean_dec_ref(v_keys_2836_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_x_2844_, v_x_2845_, v_x_2846_, v_x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2849_, lean_object* v___y_2850_){
_start:
{
uint8_t v___x_2852_; 
v___x_2852_ = l_Lean_Expr_hasMVar(v_e_2849_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_e_2849_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v_mctx_2855_; lean_object* v___x_2856_; lean_object* v_fst_2857_; lean_object* v_snd_2858_; lean_object* v___x_2859_; lean_object* v_cache_2860_; lean_object* v_zetaDeltaFVarIds_2861_; lean_object* v_postponed_2862_; lean_object* v_diag_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2872_; 
v___x_2854_ = lean_st_ref_get(v___y_2850_);
v_mctx_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_ref(v_mctx_2855_);
lean_dec(v___x_2854_);
v___x_2856_ = l_Lean_instantiateMVarsCore(v_mctx_2855_, v_e_2849_);
v_fst_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_fst_2857_);
v_snd_2858_ = lean_ctor_get(v___x_2856_, 1);
lean_inc(v_snd_2858_);
lean_dec_ref(v___x_2856_);
v___x_2859_ = lean_st_ref_take(v___y_2850_);
v_cache_2860_ = lean_ctor_get(v___x_2859_, 1);
v_zetaDeltaFVarIds_2861_ = lean_ctor_get(v___x_2859_, 2);
v_postponed_2862_ = lean_ctor_get(v___x_2859_, 3);
v_diag_2863_ = lean_ctor_get(v___x_2859_, 4);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v___x_2859_, 0);
lean_dec(v_unused_2873_);
v___x_2865_ = v___x_2859_;
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_diag_2863_);
lean_inc(v_postponed_2862_);
lean_inc(v_zetaDeltaFVarIds_2861_);
lean_inc(v_cache_2860_);
lean_dec(v___x_2859_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v_snd_2858_);
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_snd_2858_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_cache_2860_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_zetaDeltaFVarIds_2861_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_postponed_2862_);
lean_ctor_set(v_reuseFailAlloc_2871_, 4, v_diag_2863_);
v___x_2868_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = lean_st_ref_put(v___y_2850_, v___x_2868_);
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v_fst_2857_);
return v___x_2870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2874_, v___y_2875_);
lean_dec(v___y_2875_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2878_, v___y_2882_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2895_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_21080__overap_2906_; lean_object* v___x_2907_; 
v___x_2905_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_21080__overap_2906_ = lean_panic_fn_borrowed(v___x_2905_, v_msg_2897_);
lean_inc(v___y_2903_);
lean_inc_ref(v___y_2902_);
lean_inc(v___y_2901_);
lean_inc_ref(v___y_2900_);
lean_inc(v___y_2899_);
lean_inc_ref(v___y_2898_);
v___x_2907_ = lean_apply_7(v___x_21080__overap_2906_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, lean_box(0));
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object* v_a_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object* v_a_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_00_u03b1_2935_, lean_object* v_a_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_00_u03b1_2945_, lean_object* v_a_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_00_u03b1_2945_, v_a_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object* v_k_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v_b_2958_, lean_object* v_c_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2962_);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2957_);
lean_inc_ref(v___y_2956_);
v___x_2965_ = lean_apply_9(v_k_2955_, v_b_2958_, v_c_2959_, v___y_2956_, v___y_2957_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, lean_box(0));
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object* v_k_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v_b_2969_, lean_object* v_c_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_2966_, v___y_2967_, v___y_2968_, v_b_2969_, v_c_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_type_2977_, lean_object* v_k_2978_, uint8_t v_cleanupAnnotations_2979_, uint8_t v_whnfType_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___f_2988_; lean_object* v___x_2989_; 
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2981_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2988_, 0, v_k_2978_);
lean_closure_set(v___f_2988_, 1, v___y_2981_);
lean_closure_set(v___f_2988_, 2, v___y_2982_);
v___x_2989_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2977_, v___f_2988_, v_cleanupAnnotations_2979_, v_whnfType_2980_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
if (lean_obj_tag(v___x_2989_) == 0)
{
return v___x_2989_;
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_type_2998_, lean_object* v_k_2999_, lean_object* v_cleanupAnnotations_3000_, lean_object* v_whnfType_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3009_; uint8_t v_whnfType_boxed_3010_; lean_object* v_res_3011_; 
v_cleanupAnnotations_boxed_3009_ = lean_unbox(v_cleanupAnnotations_3000_);
v_whnfType_boxed_3010_ = lean_unbox(v_whnfType_3001_);
v_res_3011_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_2998_, v_k_2999_, v_cleanupAnnotations_boxed_3009_, v_whnfType_boxed_3010_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_3012_, lean_object* v_type_3013_, lean_object* v_k_3014_, uint8_t v_cleanupAnnotations_3015_, uint8_t v_whnfType_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3013_, v_k_3014_, v_cleanupAnnotations_3015_, v_whnfType_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_3025_, lean_object* v_type_3026_, lean_object* v_k_3027_, lean_object* v_cleanupAnnotations_3028_, lean_object* v_whnfType_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3037_; uint8_t v_whnfType_boxed_3038_; lean_object* v_res_3039_; 
v_cleanupAnnotations_boxed_3037_ = lean_unbox(v_cleanupAnnotations_3028_);
v_whnfType_boxed_3038_ = lean_unbox(v_whnfType_3029_);
v_res_3039_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_3025_, v_type_3026_, v_k_3027_, v_cleanupAnnotations_boxed_3037_, v_whnfType_boxed_3038_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
return v_res_3039_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3042_ = l_Lean_stringToMessageData(v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v_x_3053_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v___x_3062_, lean_object* v_fst_3063_, lean_object* v_____r_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = l_Lean_mkAppN(v___x_3062_, v_fst_3063_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v___x_3074_, lean_object* v_fst_3075_, lean_object* v_____r_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3074_, v_fst_3075_, v_____r_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v_fst_3075_);
return v_res_3084_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0));
v___x_3087_ = l_Lean_stringToMessageData(v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v_ctorName_3088_, uint8_t v___x_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3098_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1);
v___x_3099_ = l_Lean_MessageData_ofConstName(v_ctorName_3088_, v___x_3089_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v_ctorName_3104_, lean_object* v___x_3105_, lean_object* v_x_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
uint8_t v___x_25954__boxed_3114_; lean_object* v_res_3115_; 
v___x_25954__boxed_3114_ = lean_unbox(v___x_3105_);
v_res_3115_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3104_, v___x_25954__boxed_3114_, v_x_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v_x_3106_);
return v_res_3115_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object* v_e_3116_){
_start:
{
if (lean_obj_tag(v_e_3116_) == 0)
{
uint8_t v___x_3117_; 
v___x_3117_ = 2;
return v___x_3117_;
}
else
{
lean_object* v_a_3118_; uint8_t v___x_3119_; 
v_a_3118_ = lean_ctor_get(v_e_3116_, 0);
v___x_3119_ = l_Lean_Expr_hasSyntheticSorry(v_a_3118_);
if (v___x_3119_ == 0)
{
uint8_t v___x_3120_; 
v___x_3120_ = 0;
return v___x_3120_;
}
else
{
uint8_t v___x_3121_; 
v___x_3121_ = 1;
return v___x_3121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object* v_e_3122_){
_start:
{
uint8_t v_res_3123_; lean_object* v_r_3124_; 
v_res_3123_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3122_);
lean_dec_ref(v_e_3122_);
v_r_3124_ = lean_box(v_res_3123_);
return v_r_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v_cls_3125_, uint8_t v_collapsed_3126_, lean_object* v_tag_3127_, lean_object* v_opts_3128_, uint8_t v_clsEnabled_3129_, lean_object* v_oldTraces_3130_, lean_object* v_msg_3131_, lean_object* v_resStartStop_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_fst_3140_; lean_object* v_snd_3141_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v_data_3145_; lean_object* v_fst_3156_; lean_object* v_snd_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___y_3161_; lean_object* v_a_3162_; uint8_t v___y_3177_; double v___y_3209_; 
v_fst_3140_ = lean_ctor_get(v_resStartStop_3132_, 0);
lean_inc(v_fst_3140_);
v_snd_3141_ = lean_ctor_get(v_resStartStop_3132_, 1);
lean_inc(v_snd_3141_);
lean_dec_ref(v_resStartStop_3132_);
v_fst_3156_ = lean_ctor_get(v_snd_3141_, 0);
lean_inc(v_fst_3156_);
v_snd_3157_ = lean_ctor_get(v_snd_3141_, 1);
lean_inc(v_snd_3157_);
lean_dec(v_snd_3141_);
v___x_3158_ = l_Lean_trace_profiler;
v___x_3159_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3128_, v___x_3158_);
if (v___x_3159_ == 0)
{
v___y_3177_ = v___x_3159_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3215_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3128_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; double v___x_3218_; double v___x_3219_; double v___x_3220_; 
v___x_3216_ = l_Lean_trace_profiler_threshold;
v___x_3217_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3128_, v___x_3216_);
v___x_3218_ = lean_float_of_nat(v___x_3217_);
v___x_3219_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_3220_ = lean_float_div(v___x_3218_, v___x_3219_);
v___y_3209_ = v___x_3220_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; double v___x_3223_; 
v___x_3221_ = l_Lean_trace_profiler_threshold;
v___x_3222_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3128_, v___x_3221_);
v___x_3223_ = lean_float_of_nat(v___x_3222_);
v___y_3209_ = v___x_3223_;
goto v___jp_3208_;
}
}
v___jp_3142_:
{
lean_object* v___x_3146_; 
lean_inc(v___y_3143_);
v___x_3146_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_3130_, v_data_3145_, v___y_3143_, v___y_3144_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v___x_3147_; 
lean_dec_ref_known(v___x_3146_, 1);
v___x_3147_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3140_);
return v___x_3147_;
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_fst_3140_);
v_a_3148_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3146_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3146_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
v___jp_3160_:
{
uint8_t v_result_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; double v___x_3166_; lean_object* v_data_3167_; 
v_result_3163_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_fst_3140_);
v___x_3164_ = lean_box(v_result_3163_);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
v___x_3166_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3127_);
lean_inc_ref(v___x_3165_);
lean_inc(v_cls_3125_);
v_data_3167_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3167_, 0, v_cls_3125_);
lean_ctor_set(v_data_3167_, 1, v___x_3165_);
lean_ctor_set(v_data_3167_, 2, v_tag_3127_);
lean_ctor_set_float(v_data_3167_, sizeof(void*)*3, v___x_3166_);
lean_ctor_set_float(v_data_3167_, sizeof(void*)*3 + 8, v___x_3166_);
lean_ctor_set_uint8(v_data_3167_, sizeof(void*)*3 + 16, v_collapsed_3126_);
if (v___x_3159_ == 0)
{
lean_dec_ref_known(v___x_3165_, 1);
lean_dec(v_snd_3157_);
lean_dec(v_fst_3156_);
lean_dec_ref(v_tag_3127_);
lean_dec(v_cls_3125_);
v___y_3143_ = v___y_3161_;
v___y_3144_ = v_a_3162_;
v_data_3145_ = v_data_3167_;
goto v___jp_3142_;
}
else
{
lean_object* v_data_3168_; double v___x_3169_; double v___x_3170_; 
lean_dec_ref_known(v_data_3167_, 3);
v_data_3168_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3168_, 0, v_cls_3125_);
lean_ctor_set(v_data_3168_, 1, v___x_3165_);
lean_ctor_set(v_data_3168_, 2, v_tag_3127_);
v___x_3169_ = lean_unbox_float(v_fst_3156_);
lean_dec(v_fst_3156_);
lean_ctor_set_float(v_data_3168_, sizeof(void*)*3, v___x_3169_);
v___x_3170_ = lean_unbox_float(v_snd_3157_);
lean_dec(v_snd_3157_);
lean_ctor_set_float(v_data_3168_, sizeof(void*)*3 + 8, v___x_3170_);
lean_ctor_set_uint8(v_data_3168_, sizeof(void*)*3 + 16, v_collapsed_3126_);
v___y_3143_ = v___y_3161_;
v___y_3144_ = v_a_3162_;
v_data_3145_ = v_data_3168_;
goto v___jp_3142_;
}
}
v___jp_3171_:
{
lean_object* v_ref_3172_; lean_object* v___x_3173_; 
v_ref_3172_ = lean_ctor_get(v___y_3137_, 2);
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v_fst_3140_);
v___x_3173_ = lean_apply_8(v_msg_3131_, v_fst_3140_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref_known(v___x_3173_, 1);
v___y_3161_ = v_ref_3172_;
v_a_3162_ = v_a_3174_;
goto v___jp_3160_;
}
else
{
lean_object* v___x_3175_; 
lean_dec_ref_known(v___x_3173_, 1);
v___x_3175_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_3161_ = v_ref_3172_;
v_a_3162_ = v___x_3175_;
goto v___jp_3160_;
}
}
v___jp_3176_:
{
if (v_clsEnabled_3129_ == 0)
{
if (v___y_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v_traceState_3179_; lean_object* v_env_3180_; lean_object* v_nextMacroScope_3181_; lean_object* v_ngen_3182_; lean_object* v_auxDeclNGen_3183_; lean_object* v_cache_3184_; lean_object* v_recordedDeps_3185_; lean_object* v_messages_3186_; lean_object* v_infoState_3187_; lean_object* v_snapshotTasks_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_snd_3157_);
lean_dec(v_fst_3156_);
lean_dec_ref(v_msg_3131_);
lean_dec_ref(v_tag_3127_);
lean_dec(v_cls_3125_);
v___x_3178_ = lean_st_ref_take(v___y_3138_);
v_traceState_3179_ = lean_ctor_get(v___x_3178_, 4);
v_env_3180_ = lean_ctor_get(v___x_3178_, 0);
v_nextMacroScope_3181_ = lean_ctor_get(v___x_3178_, 1);
v_ngen_3182_ = lean_ctor_get(v___x_3178_, 2);
v_auxDeclNGen_3183_ = lean_ctor_get(v___x_3178_, 3);
v_cache_3184_ = lean_ctor_get(v___x_3178_, 5);
v_recordedDeps_3185_ = lean_ctor_get(v___x_3178_, 6);
v_messages_3186_ = lean_ctor_get(v___x_3178_, 7);
v_infoState_3187_ = lean_ctor_get(v___x_3178_, 8);
v_snapshotTasks_3188_ = lean_ctor_get(v___x_3178_, 9);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3190_ = v___x_3178_;
v_isShared_3191_ = v_isSharedCheck_3207_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_snapshotTasks_3188_);
lean_inc(v_infoState_3187_);
lean_inc(v_messages_3186_);
lean_inc(v_recordedDeps_3185_);
lean_inc(v_cache_3184_);
lean_inc(v_traceState_3179_);
lean_inc(v_auxDeclNGen_3183_);
lean_inc(v_ngen_3182_);
lean_inc(v_nextMacroScope_3181_);
lean_inc(v_env_3180_);
lean_dec(v___x_3178_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3207_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
uint64_t v_tid_3192_; lean_object* v_traces_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3206_; 
v_tid_3192_ = lean_ctor_get_uint64(v_traceState_3179_, sizeof(void*)*1);
v_traces_3193_ = lean_ctor_get(v_traceState_3179_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_traceState_3179_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3195_ = v_traceState_3179_;
v_isShared_3196_ = v_isSharedCheck_3206_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_traces_3193_);
lean_dec(v_traceState_3179_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3206_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3197_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3130_, v_traces_3193_);
lean_dec_ref(v_traces_3193_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3197_);
v___x_3199_ = v___x_3195_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3197_);
lean_ctor_set_uint64(v_reuseFailAlloc_3205_, sizeof(void*)*1, v_tid_3192_);
v___x_3199_ = v_reuseFailAlloc_3205_;
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
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_env_3180_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_nextMacroScope_3181_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v_ngen_3182_);
lean_ctor_set(v_reuseFailAlloc_3204_, 3, v_auxDeclNGen_3183_);
lean_ctor_set(v_reuseFailAlloc_3204_, 4, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3204_, 5, v_cache_3184_);
lean_ctor_set(v_reuseFailAlloc_3204_, 6, v_recordedDeps_3185_);
lean_ctor_set(v_reuseFailAlloc_3204_, 7, v_messages_3186_);
lean_ctor_set(v_reuseFailAlloc_3204_, 8, v_infoState_3187_);
lean_ctor_set(v_reuseFailAlloc_3204_, 9, v_snapshotTasks_3188_);
v___x_3201_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_st_ref_put(v___y_3138_, v___x_3201_);
v___x_3203_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3140_);
return v___x_3203_;
}
}
}
}
}
else
{
goto v___jp_3171_;
}
}
else
{
goto v___jp_3171_;
}
}
v___jp_3208_:
{
double v___x_3210_; double v___x_3211_; double v___x_3212_; uint8_t v___x_3213_; 
v___x_3210_ = lean_unbox_float(v_snd_3157_);
v___x_3211_ = lean_unbox_float(v_fst_3156_);
v___x_3212_ = lean_float_sub(v___x_3210_, v___x_3211_);
v___x_3213_ = lean_float_decLt(v___y_3209_, v___x_3212_);
v___y_3177_ = v___x_3213_;
goto v___jp_3176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v_cls_3224_, lean_object* v_collapsed_3225_, lean_object* v_tag_3226_, lean_object* v_opts_3227_, lean_object* v_clsEnabled_3228_, lean_object* v_oldTraces_3229_, lean_object* v_msg_3230_, lean_object* v_resStartStop_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v_collapsed_boxed_3239_; uint8_t v_clsEnabled_boxed_3240_; lean_object* v_res_3241_; 
v_collapsed_boxed_3239_ = lean_unbox(v_collapsed_3225_);
v_clsEnabled_boxed_3240_ = lean_unbox(v_clsEnabled_3228_);
v_res_3241_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3224_, v_collapsed_boxed_3239_, v_tag_3226_, v_opts_3227_, v_clsEnabled_boxed_3240_, v_oldTraces_3229_, v_msg_3230_, v_resStartStop_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec_ref(v_opts_3227_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v___x_3242_, lean_object* v_as_3243_, size_t v_i_3244_, size_t v_stop_3245_, lean_object* v_b_3246_){
_start:
{
lean_object* v___y_3248_; uint8_t v___x_3252_; 
v___x_3252_ = lean_usize_dec_eq(v_i_3244_, v_stop_3245_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = lean_array_uget_borrowed(v_as_3243_, v_i_3244_);
v___x_3254_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v___x_3242_, v___x_3253_);
if (v___x_3254_ == 0)
{
v___y_3248_ = v_b_3246_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3255_; 
lean_inc(v___x_3253_);
v___x_3255_ = lean_array_push(v_b_3246_, v___x_3253_);
v___y_3248_ = v___x_3255_;
goto v___jp_3247_;
}
}
else
{
return v_b_3246_;
}
v___jp_3247_:
{
size_t v___x_3249_; size_t v___x_3250_; 
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_add(v_i_3244_, v___x_3249_);
v_i_3244_ = v___x_3250_;
v_b_3246_ = v___y_3248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v___x_3256_, lean_object* v_as_3257_, lean_object* v_i_3258_, lean_object* v_stop_3259_, lean_object* v_b_3260_){
_start:
{
size_t v_i_boxed_3261_; size_t v_stop_boxed_3262_; lean_object* v_res_3263_; 
v_i_boxed_3261_ = lean_unbox_usize(v_i_3258_);
lean_dec(v_i_3258_);
v_stop_boxed_3262_ = lean_unbox_usize(v_stop_3259_);
lean_dec(v_stop_3259_);
v_res_3263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3256_, v_as_3257_, v_i_boxed_3261_, v_stop_boxed_3262_, v_b_3260_);
lean_dec_ref(v_as_3257_);
lean_dec_ref(v___x_3256_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
if (lean_obj_tag(v_a_3264_) == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = l_List_reverse___redArg(v_a_3265_);
return v___x_3266_;
}
else
{
lean_object* v_head_3267_; lean_object* v_tail_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3277_; 
v_head_3267_ = lean_ctor_get(v_a_3264_, 0);
v_tail_3268_ = lean_ctor_get(v_a_3264_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_a_3264_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3270_ = v_a_3264_;
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_tail_3268_);
lean_inc(v_head_3267_);
lean_dec(v_a_3264_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = l_Lean_MessageData_ofExpr(v_head_3267_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 1, v_a_3265_);
lean_ctor_set(v___x_3270_, 0, v___x_3272_);
v___x_3274_ = v___x_3270_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_a_3265_);
v___x_3274_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
v_a_3264_ = v_tail_3268_;
v_a_3265_ = v___x_3274_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3281_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3282_ = lean_unsigned_to_nat(6u);
v___x_3283_ = lean_unsigned_to_nat(108u);
v___x_3284_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3286_ = l_mkPanicMessageWithDecl(v___x_3285_, v___x_3284_, v___x_3283_, v___x_3282_, v___x_3281_);
return v___x_3286_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3297_ = l_Lean_stringToMessageData(v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_unsigned_to_nat(16u);
v___x_3300_ = lean_mk_array(v___x_3299_, v___x_3298_);
return v___x_3300_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12));
v___x_3303_ = l_Lean_stringToMessageData(v___x_3302_);
return v___x_3303_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14));
v___x_3306_ = l_Lean_stringToMessageData(v___x_3305_);
return v___x_3306_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3317_, lean_object* v_us_3318_, lean_object* v_xs_3319_, lean_object* v___x_3320_, lean_object* v___x_3321_, lean_object* v_ctorName_3322_, lean_object* v___x_3323_, lean_object* v___f_3324_, lean_object* v_insts_3325_, lean_object* v_localInst2Index_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; lean_object* v_type_3335_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; uint8_t v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; uint8_t v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v_val_3468_; lean_object* v___y_3495_; lean_object* v___y_3506_; lean_object* v___x_3516_; lean_object* v_env_3517_; uint8_t v___x_3518_; uint8_t v___x_3519_; 
lean_inc(v_us_3318_);
lean_inc(v_inductiveTypeName_3317_);
v___x_3334_ = l_Lean_Expr_const___override(v_inductiveTypeName_3317_, v_us_3318_);
v_type_3335_ = l_Lean_mkAppN(v___x_3334_, v_xs_3319_);
v___x_3516_ = lean_st_ref_get(v___y_3332_);
v_env_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc_ref(v_env_3517_);
lean_dec(v___x_3516_);
v___x_3518_ = l_Lean_isStructure(v_env_3517_, v_inductiveTypeName_3317_);
v___x_3519_ = 1;
if (v___x_3518_ == 0)
{
lean_object* v_toCold_3520_; lean_object* v_options_3521_; lean_object* v_inheritedTraceOptions_3522_; uint8_t v_hasTrace_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref(v___f_3324_);
v_toCold_3520_ = lean_ctor_get(v___y_3331_, 0);
v_options_3521_ = lean_ctor_get(v_toCold_3520_, 2);
v_inheritedTraceOptions_3522_ = lean_ctor_get(v_toCold_3520_, 11);
v_hasTrace_3523_ = lean_ctor_get_uint8(v_options_3521_, sizeof(void*)*1);
lean_inc(v_ctorName_3322_);
v___x_3524_ = l_Lean_Expr_const___override(v_ctorName_3322_, v_us_3318_);
v___x_3525_ = l_Lean_mkAppN(v___x_3524_, v___x_3323_);
if (v_hasTrace_3523_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v_ctorName_3322_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
lean_inc_ref(v___x_3525_);
v___x_3526_ = lean_infer_type(v___x_3525_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = lean_box(0);
v___x_3529_ = 0;
v___x_3530_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3527_, v___x_3528_, v___x_3529_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v_snd_3532_; lean_object* v_fst_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3576_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v_snd_3532_ = lean_ctor_get(v_a_3531_, 1);
v_fst_3533_ = lean_ctor_get(v_a_3531_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_a_3531_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3535_ = v_a_3531_;
v_isShared_3536_ = v_isSharedCheck_3576_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_snd_3532_);
lean_inc(v_fst_3533_);
lean_dec(v_a_3531_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3576_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v_snd_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3574_; 
v_snd_3537_ = lean_ctor_get(v_snd_3532_, 1);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_snd_3532_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; 
v_unused_3575_ = lean_ctor_get(v_snd_3532_, 0);
lean_dec(v_unused_3575_);
v___x_3539_ = v_snd_3532_;
v_isShared_3540_ = v_isSharedCheck_3574_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_snd_3537_);
lean_dec(v_snd_3532_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3574_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; 
lean_inc(v_snd_3537_);
lean_inc_ref(v_type_3335_);
v___x_3541_ = l_Lean_Meta_isExprDefEq(v_type_3335_, v_snd_3537_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; uint8_t v___x_3543_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = lean_unbox(v_a_3542_);
lean_dec(v_a_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
lean_dec(v_fst_3533_);
lean_dec_ref(v___x_3525_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v___x_3544_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3545_ = l_Lean_indentExpr(v_type_3335_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 7);
lean_ctor_set(v___x_3539_, 1, v___x_3545_);
lean_ctor_set(v___x_3539_, 0, v___x_3544_);
v___x_3547_ = v___x_3539_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3536_ == 0)
{
lean_ctor_set_tag(v___x_3535_, 7);
lean_ctor_set(v___x_3535_, 1, v___x_3548_);
lean_ctor_set(v___x_3535_, 0, v___x_3547_);
v___x_3550_ = v___x_3535_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
v___x_3551_ = l_Lean_indentExpr(v_snd_3537_);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3552_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_del_object(v___x_3539_);
lean_dec(v_snd_3537_);
lean_del_object(v___x_3535_);
v___x_3564_ = lean_box(0);
v___x_3565_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3525_, v_fst_3533_, v___x_3564_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v_fst_3533_);
v___y_3506_ = v___x_3565_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_del_object(v___x_3539_);
lean_dec(v_snd_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_fst_3533_);
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3566_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3541_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3541_);
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
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3577_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3530_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3530_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3585_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3526_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3526_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_object* v___x_3593_; lean_object* v___f_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v_a_3602_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v_a_3617_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v_a_3634_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v_a_3646_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; 
v___x_3593_ = lean_box(v___x_3518_);
v___f_3594_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3594_, 0, v_ctorName_3322_);
lean_closure_set(v___f_3594_, 1, v___x_3593_);
v___x_3595_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3596_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3597_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3598_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3522_, v_options_3521_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3745_; uint8_t v___x_3746_; 
v___x_3745_ = l_Lean_trace_profiler;
v___x_3746_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3521_, v___x_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_dec_ref(v___f_3594_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
lean_inc_ref(v___x_3525_);
v___x_3747_ = lean_infer_type(v___x_3525_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; lean_object* v___x_3751_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
lean_dec_ref_known(v___x_3747_, 1);
v___x_3749_ = lean_box(0);
v___x_3750_ = 0;
v___x_3751_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3748_, v___x_3749_, v___x_3750_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v_snd_3753_; lean_object* v_fst_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3797_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v_snd_3753_ = lean_ctor_get(v_a_3752_, 1);
v_fst_3754_ = lean_ctor_get(v_a_3752_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_a_3752_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3756_ = v_a_3752_;
v_isShared_3757_ = v_isSharedCheck_3797_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_snd_3753_);
lean_inc(v_fst_3754_);
lean_dec(v_a_3752_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3797_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v_snd_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3795_; 
v_snd_3758_ = lean_ctor_get(v_snd_3753_, 1);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_snd_3753_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; 
v_unused_3796_ = lean_ctor_get(v_snd_3753_, 0);
lean_dec(v_unused_3796_);
v___x_3760_ = v_snd_3753_;
v_isShared_3761_ = v_isSharedCheck_3795_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_snd_3758_);
lean_dec(v_snd_3753_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3795_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; 
lean_inc(v_snd_3758_);
lean_inc_ref(v_type_3335_);
v___x_3762_ = l_Lean_Meta_isExprDefEq(v_type_3335_, v_snd_3758_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; uint8_t v___x_3764_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref_known(v___x_3762_, 1);
v___x_3764_ = lean_unbox(v_a_3763_);
lean_dec(v_a_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec(v_fst_3754_);
lean_dec_ref(v___x_3525_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v___x_3765_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3766_ = l_Lean_indentExpr(v_type_3335_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set_tag(v___x_3760_, 7);
lean_ctor_set(v___x_3760_, 1, v___x_3766_);
lean_ctor_set(v___x_3760_, 0, v___x_3765_);
v___x_3768_ = v___x_3760_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3769_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3757_ == 0)
{
lean_ctor_set_tag(v___x_3756_, 7);
lean_ctor_set(v___x_3756_, 1, v___x_3769_);
lean_ctor_set(v___x_3756_, 0, v___x_3768_);
v___x_3771_ = v___x_3756_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v___x_3772_ = l_Lean_indentExpr(v_snd_3758_);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3773_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3774_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3774_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_del_object(v___x_3760_);
lean_dec(v_snd_3758_);
lean_del_object(v___x_3756_);
v___x_3785_ = lean_box(0);
v___x_3786_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3525_, v_fst_3754_, v___x_3785_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v_fst_3754_);
v___y_3506_ = v___x_3786_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_del_object(v___x_3760_);
lean_dec(v_snd_3758_);
lean_del_object(v___x_3756_);
lean_dec(v_fst_3754_);
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3787_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3762_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3762_);
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
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3798_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3751_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3751_);
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
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3806_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3747_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3747_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
goto v___jp_3660_;
}
}
else
{
goto v___jp_3660_;
}
v___jp_3599_:
{
lean_object* v___x_3603_; double v___x_3604_; double v___x_3605_; double v___x_3606_; double v___x_3607_; double v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3603_ = lean_io_mono_nanos_now();
v___x_3604_ = lean_float_of_nat(v___y_3600_);
v___x_3605_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3606_ = lean_float_div(v___x_3604_, v___x_3605_);
v___x_3607_ = lean_float_of_nat(v___x_3603_);
v___x_3608_ = lean_float_div(v___x_3607_, v___x_3605_);
v___x_3609_ = lean_box_float(v___x_3606_);
v___x_3610_ = lean_box_float(v___x_3608_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v_a_3602_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3595_, v___x_3519_, v___x_3596_, v_options_3521_, v___x_3598_, v___y_3601_, v___f_3594_, v___x_3612_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v___y_3506_ = v___x_3613_;
goto v___jp_3505_;
}
v___jp_3614_:
{
lean_object* v___x_3618_; 
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v_a_3617_);
v___y_3600_ = v___y_3615_;
v___y_3601_ = v___y_3616_;
v_a_3602_ = v___x_3618_;
goto v___jp_3599_;
}
v___jp_3619_:
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
v_a_3623_ = lean_ctor_get(v___y_3622_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___y_3622_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___y_3622_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___y_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 1);
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
v___y_3600_ = v___y_3620_;
v___y_3601_ = v___y_3621_;
v_a_3602_ = v___x_3628_;
goto v___jp_3599_;
}
}
}
v___jp_3631_:
{
lean_object* v___x_3635_; double v___x_3636_; double v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3635_ = lean_io_get_num_heartbeats();
v___x_3636_ = lean_float_of_nat(v___y_3632_);
v___x_3637_ = lean_float_of_nat(v___x_3635_);
v___x_3638_ = lean_box_float(v___x_3636_);
v___x_3639_ = lean_box_float(v___x_3637_);
v___x_3640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v_a_3634_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3595_, v___x_3519_, v___x_3596_, v_options_3521_, v___x_3598_, v___y_3633_, v___f_3594_, v___x_3641_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v___y_3506_ = v___x_3642_;
goto v___jp_3505_;
}
v___jp_3643_:
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v_a_3646_);
v___y_3632_ = v___y_3644_;
v___y_3633_ = v___y_3645_;
v_a_3634_ = v___x_3647_;
goto v___jp_3631_;
}
v___jp_3648_:
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_a_3652_ = lean_ctor_get(v___y_3651_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___y_3651_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___y_3651_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___y_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 1);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
v___y_3632_ = v___y_3649_;
v___y_3633_ = v___y_3650_;
v_a_3634_ = v___x_3657_;
goto v___jp_3631_;
}
}
}
v___jp_3660_:
{
lean_object* v___x_3661_; lean_object* v_a_3662_; lean_object* v___x_3663_; uint8_t v___x_3664_; 
v___x_3661_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3332_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
v___x_3663_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3664_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3521_, v___x_3663_);
if (v___x_3664_ == 0)
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_io_mono_nanos_now();
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
lean_inc_ref(v___x_3525_);
v___x_3666_ = lean_infer_type(v___x_3525_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = lean_box(0);
v___x_3669_ = 0;
v___x_3670_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3667_, v___x_3668_, v___x_3669_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v_snd_3672_; lean_object* v_fst_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3702_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v_snd_3672_ = lean_ctor_get(v_a_3671_, 1);
v_fst_3673_ = lean_ctor_get(v_a_3671_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_a_3671_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3675_ = v_a_3671_;
v_isShared_3676_ = v_isSharedCheck_3702_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_snd_3672_);
lean_inc(v_fst_3673_);
lean_dec(v_a_3671_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3702_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_snd_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3700_; 
v_snd_3677_ = lean_ctor_get(v_snd_3672_, 1);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_snd_3672_);
if (v_isSharedCheck_3700_ == 0)
{
lean_object* v_unused_3701_; 
v_unused_3701_ = lean_ctor_get(v_snd_3672_, 0);
lean_dec(v_unused_3701_);
v___x_3679_ = v_snd_3672_;
v_isShared_3680_ = v_isSharedCheck_3700_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_snd_3677_);
lean_dec(v_snd_3672_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3700_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; 
lean_inc(v_snd_3677_);
lean_inc_ref(v_type_3335_);
v___x_3681_ = l_Lean_Meta_isExprDefEq(v_type_3335_, v_snd_3677_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; uint8_t v___x_3683_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v___x_3681_, 1);
v___x_3683_ = lean_unbox(v_a_3682_);
lean_dec(v_a_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_dec(v_fst_3673_);
lean_dec_ref(v___x_3525_);
v___x_3684_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3335_);
v___x_3685_ = l_Lean_indentExpr(v_type_3335_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set_tag(v___x_3679_, 7);
lean_ctor_set(v___x_3679_, 1, v___x_3685_);
lean_ctor_set(v___x_3679_, 0, v___x_3684_);
v___x_3687_ = v___x_3679_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 7);
lean_ctor_set(v___x_3675_, 1, v___x_3688_);
lean_ctor_set(v___x_3675_, 0, v___x_3687_);
v___x_3690_ = v___x_3675_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v_a_3694_; 
v___x_3691_ = l_Lean_indentExpr(v_snd_3677_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3692_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref(v___x_3693_);
v___y_3615_ = v___x_3665_;
v___y_3616_ = v_a_3662_;
v_a_3617_ = v_a_3694_;
goto v___jp_3614_;
}
}
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_del_object(v___x_3679_);
lean_dec(v_snd_3677_);
lean_del_object(v___x_3675_);
v___x_3697_ = lean_box(0);
v___x_3698_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3525_, v_fst_3673_, v___x_3697_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v_fst_3673_);
v___y_3620_ = v___x_3665_;
v___y_3621_ = v_a_3662_;
v___y_3622_ = v___x_3698_;
goto v___jp_3619_;
}
}
else
{
lean_object* v_a_3699_; 
lean_del_object(v___x_3679_);
lean_dec(v_snd_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_fst_3673_);
lean_dec_ref(v___x_3525_);
v_a_3699_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3681_, 1);
v___y_3615_ = v___x_3665_;
v___y_3616_ = v_a_3662_;
v_a_3617_ = v_a_3699_;
goto v___jp_3614_;
}
}
}
}
else
{
lean_object* v_a_3703_; 
lean_dec_ref(v___x_3525_);
v_a_3703_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3703_);
lean_dec_ref_known(v___x_3670_, 1);
v___y_3615_ = v___x_3665_;
v___y_3616_ = v_a_3662_;
v_a_3617_ = v_a_3703_;
goto v___jp_3614_;
}
}
else
{
lean_object* v_a_3704_; 
lean_dec_ref(v___x_3525_);
v_a_3704_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3666_, 1);
v___y_3615_ = v___x_3665_;
v___y_3616_ = v_a_3662_;
v_a_3617_ = v_a_3704_;
goto v___jp_3614_;
}
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
lean_inc_ref(v___x_3525_);
v___x_3706_ = lean_infer_type(v___x_3525_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3708_ = lean_box(0);
v___x_3709_ = 0;
v___x_3710_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3707_, v___x_3708_, v___x_3709_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v_snd_3712_; lean_object* v_fst_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3742_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v_snd_3712_ = lean_ctor_get(v_a_3711_, 1);
v_fst_3713_ = lean_ctor_get(v_a_3711_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_a_3711_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3715_ = v_a_3711_;
v_isShared_3716_ = v_isSharedCheck_3742_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_snd_3712_);
lean_inc(v_fst_3713_);
lean_dec(v_a_3711_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3742_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_snd_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3740_; 
v_snd_3717_ = lean_ctor_get(v_snd_3712_, 1);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_snd_3712_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; 
v_unused_3741_ = lean_ctor_get(v_snd_3712_, 0);
lean_dec(v_unused_3741_);
v___x_3719_ = v_snd_3712_;
v_isShared_3720_ = v_isSharedCheck_3740_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_snd_3717_);
lean_dec(v_snd_3712_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3740_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; 
lean_inc(v_snd_3717_);
lean_inc_ref(v_type_3335_);
v___x_3721_ = l_Lean_Meta_isExprDefEq(v_type_3335_, v_snd_3717_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; uint8_t v___x_3723_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___x_3723_ = lean_unbox(v_a_3722_);
lean_dec(v_a_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_dec(v_fst_3713_);
lean_dec_ref(v___x_3525_);
v___x_3724_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3335_);
v___x_3725_ = l_Lean_indentExpr(v_type_3335_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set_tag(v___x_3719_, 7);
lean_ctor_set(v___x_3719_, 1, v___x_3725_);
lean_ctor_set(v___x_3719_, 0, v___x_3724_);
v___x_3727_ = v___x_3719_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3716_ == 0)
{
lean_ctor_set_tag(v___x_3715_, 7);
lean_ctor_set(v___x_3715_, 1, v___x_3728_);
lean_ctor_set(v___x_3715_, 0, v___x_3727_);
v___x_3730_ = v___x_3715_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v_a_3734_; 
v___x_3731_ = l_Lean_indentExpr(v_snd_3717_);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3732_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___x_3733_);
v___y_3644_ = v___x_3705_;
v___y_3645_ = v_a_3662_;
v_a_3646_ = v_a_3734_;
goto v___jp_3643_;
}
}
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_del_object(v___x_3719_);
lean_dec(v_snd_3717_);
lean_del_object(v___x_3715_);
v___x_3737_ = lean_box(0);
v___x_3738_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3525_, v_fst_3713_, v___x_3737_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v_fst_3713_);
v___y_3649_ = v___x_3705_;
v___y_3650_ = v_a_3662_;
v___y_3651_ = v___x_3738_;
goto v___jp_3648_;
}
}
else
{
lean_object* v_a_3739_; 
lean_del_object(v___x_3719_);
lean_dec(v_snd_3717_);
lean_del_object(v___x_3715_);
lean_dec(v_fst_3713_);
lean_dec_ref(v___x_3525_);
v_a_3739_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3721_, 1);
v___y_3644_ = v___x_3705_;
v___y_3645_ = v_a_3662_;
v_a_3646_ = v_a_3739_;
goto v___jp_3643_;
}
}
}
}
else
{
lean_object* v_a_3743_; 
lean_dec_ref(v___x_3525_);
v_a_3743_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3710_, 1);
v___y_3644_ = v___x_3705_;
v___y_3645_ = v_a_3662_;
v_a_3646_ = v_a_3743_;
goto v___jp_3643_;
}
}
else
{
lean_object* v_a_3744_; 
lean_dec_ref(v___x_3525_);
v_a_3744_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3706_, 1);
v___y_3644_ = v___x_3705_;
v___y_3645_ = v_a_3662_;
v_a_3646_ = v_a_3744_;
goto v___jp_3643_;
}
}
}
}
}
else
{
lean_object* v_toCold_3814_; lean_object* v_options_3815_; uint8_t v_hasTrace_3816_; 
lean_dec(v_ctorName_3322_);
lean_dec(v_us_3318_);
v_toCold_3814_ = lean_ctor_get(v___y_3331_, 0);
v_options_3815_ = lean_ctor_get(v_toCold_3814_, 2);
v_hasTrace_3816_ = lean_ctor_get_uint8(v_options_3815_, sizeof(void*)*1);
if (v_hasTrace_3816_ == 0)
{
lean_object* v_ref_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec_ref(v___f_3324_);
v_ref_3817_ = lean_ctor_get(v___y_3331_, 2);
v___x_3818_ = l_Lean_SourceInfo_fromRef(v_ref_3817_, v_hasTrace_3816_);
v___x_3819_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3820_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3818_);
v___x_3821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3818_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = l_Lean_Syntax_node1(v___x_3818_, v___x_3819_, v___x_3821_);
lean_inc_ref(v_type_3335_);
v___x_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3823_, 0, v_type_3335_);
v___x_3824_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3824_, 0, v___x_3822_);
lean_closure_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3824_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v___y_3495_ = v___x_3825_;
goto v___jp_3494_;
}
else
{
lean_object* v_ref_3826_; lean_object* v_inheritedTraceOptions_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v_a_3835_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_a_3850_; 
v_ref_3826_ = lean_ctor_get(v___y_3331_, 2);
v_inheritedTraceOptions_3827_ = lean_ctor_get(v_toCold_3814_, 11);
v___x_3828_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3829_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3830_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3827_, v_options_3815_, v___x_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3923_; uint8_t v___x_3924_; 
v___x_3923_ = l_Lean_trace_profiler;
v___x_3924_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3815_, v___x_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec_ref(v___f_3324_);
v___x_3925_ = l_Lean_SourceInfo_fromRef(v_ref_3826_, v___x_3924_);
v___x_3926_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3927_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3925_);
v___x_3928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3925_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3926_, v___x_3928_);
lean_inc_ref(v_type_3335_);
v___x_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3930_, 0, v_type_3335_);
v___x_3931_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3931_, 0, v___x_3929_);
lean_closure_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3931_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v___y_3495_ = v___x_3932_;
goto v___jp_3494_;
}
else
{
goto v___jp_3859_;
}
}
else
{
goto v___jp_3859_;
}
v___jp_3832_:
{
lean_object* v___x_3836_; double v___x_3837_; double v___x_3838_; double v___x_3839_; double v___x_3840_; double v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3836_ = lean_io_mono_nanos_now();
v___x_3837_ = lean_float_of_nat(v___y_3834_);
v___x_3838_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3839_ = lean_float_div(v___x_3837_, v___x_3838_);
v___x_3840_ = lean_float_of_nat(v___x_3836_);
v___x_3841_ = lean_float_div(v___x_3840_, v___x_3838_);
v___x_3842_ = lean_box_float(v___x_3839_);
v___x_3843_ = lean_box_float(v___x_3841_);
v___x_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v_a_3835_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3828_, v___x_3519_, v___x_3829_, v_options_3815_, v___x_3831_, v___y_3833_, v___f_3324_, v___x_3845_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v___y_3495_ = v___x_3846_;
goto v___jp_3494_;
}
v___jp_3847_:
{
lean_object* v___x_3851_; double v___x_3852_; double v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3851_ = lean_io_get_num_heartbeats();
v___x_3852_ = lean_float_of_nat(v___y_3849_);
v___x_3853_ = lean_float_of_nat(v___x_3851_);
v___x_3854_ = lean_box_float(v___x_3852_);
v___x_3855_ = lean_box_float(v___x_3853_);
v___x_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3854_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v_a_3850_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
v___x_3858_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3828_, v___x_3519_, v___x_3829_, v_options_3815_, v___x_3831_, v___y_3848_, v___f_3324_, v___x_3857_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v___y_3495_ = v___x_3858_;
goto v___jp_3494_;
}
v___jp_3859_:
{
lean_object* v___x_3860_; lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3922_; 
v___x_3860_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3332_);
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3922_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3922_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3865_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3866_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3815_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3867_ = lean_io_mono_nanos_now();
v___x_3868_ = l_Lean_SourceInfo_fromRef(v_ref_3826_, v___x_3866_);
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3868_);
v___x_3871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3868_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l_Lean_Syntax_node1(v___x_3868_, v___x_3869_, v___x_3871_);
lean_inc_ref(v_type_3335_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set_tag(v___x_3863_, 1);
lean_ctor_set(v___x_3863_, 0, v_type_3335_);
v___x_3874_ = v___x_3863_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_type_3335_);
v___x_3874_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3875_, 0, v___x_3872_);
lean_closure_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3875_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set_tag(v___x_3879_, 1);
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
v___y_3833_ = v_a_3861_;
v___y_3834_ = v___x_3867_;
v_a_3835_ = v___x_3882_;
goto v___jp_3832_;
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3876_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3876_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set_tag(v___x_3887_, 0);
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
v___y_3833_ = v_a_3861_;
v___y_3834_ = v___x_3867_;
v_a_3835_ = v___x_3890_;
goto v___jp_3832_;
}
}
}
}
}
else
{
lean_object* v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3894_ = lean_io_get_num_heartbeats();
v___x_3895_ = 0;
v___x_3896_ = l_Lean_SourceInfo_fromRef(v_ref_3826_, v___x_3895_);
v___x_3897_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3898_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3896_);
v___x_3899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3896_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = l_Lean_Syntax_node1(v___x_3896_, v___x_3897_, v___x_3899_);
lean_inc_ref(v_type_3335_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set_tag(v___x_3863_, 1);
lean_ctor_set(v___x_3863_, 0, v_type_3335_);
v___x_3902_ = v___x_3863_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_type_3335_);
v___x_3902_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3903_, 0, v___x_3900_);
lean_closure_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3903_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set_tag(v___x_3907_, 1);
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
v___y_3848_ = v_a_3861_;
v___y_3849_ = v___x_3894_;
v_a_3850_ = v___x_3910_;
goto v___jp_3847_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
v_a_3913_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3904_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3904_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
lean_ctor_set_tag(v___x_3915_, 0);
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
v___y_3848_ = v_a_3861_;
v___y_3849_ = v___x_3894_;
v_a_3850_ = v___x_3918_;
goto v___jp_3847_;
}
}
}
}
}
}
}
}
}
v___jp_3336_:
{
lean_object* v___x_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3345_ = l_Array_append___redArg(v_xs_3319_, v___y_3337_);
lean_dec_ref(v___y_3337_);
v___x_3346_ = 0;
v___x_3347_ = 1;
v___x_3348_ = l_Lean_Meta_mkForallFVars(v___x_3345_, v_type_3335_, v___x_3346_, v___y_3340_, v___y_3340_, v___x_3347_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v___x_3350_ = l_Lean_Meta_mkLambdaFVars(v___x_3345_, v___y_3339_, v___x_3346_, v___y_3340_, v___x_3346_, v___y_3340_, v___x_3347_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec_ref(v___x_3345_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3360_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3360_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3360_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_a_3351_);
lean_ctor_set(v___x_3355_, 1, v___y_3338_);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_a_3349_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3356_);
v___x_3358_ = v___x_3353_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3349_);
lean_dec(v___y_3338_);
v_a_3361_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3350_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3350_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec_ref(v___x_3345_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
v_a_3369_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3348_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3348_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
v___jp_3377_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___y_3382_);
lean_ctor_set(v___x_3389_, 1, v___y_3388_);
lean_inc(v___y_3387_);
v___x_3390_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3387_, v___x_3389_, v___y_3386_, v___y_3380_, v___y_3379_, v___y_3385_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_dec_ref_known(v___x_3390_, 1);
v___y_3337_ = v___y_3378_;
v___y_3338_ = v___y_3381_;
v___y_3339_ = v___y_3384_;
v___y_3340_ = v___y_3383_;
v___y_3341_ = v___y_3386_;
v___y_3342_ = v___y_3380_;
v___y_3343_ = v___y_3379_;
v___y_3344_ = v___y_3385_;
goto v___jp_3336_;
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v_type_3335_);
lean_dec_ref(v_xs_3319_);
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
v___jp_3399_:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_nat_dec_eq(v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v_type_3335_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v___x_3412_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3413_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3412_, v___y_3401_, v___y_3405_, v___y_3408_, v___y_3403_, v___y_3402_, v___y_3407_);
return v___x_3413_;
}
else
{
lean_object* v_toCold_3414_; lean_object* v_options_3415_; uint8_t v_hasTrace_3416_; 
v_toCold_3414_ = lean_ctor_get(v___y_3402_, 0);
v_options_3415_ = lean_ctor_get(v_toCold_3414_, 2);
v_hasTrace_3416_ = lean_ctor_get_uint8(v_options_3415_, sizeof(void*)*1);
if (v_hasTrace_3416_ == 0)
{
lean_dec(v___y_3409_);
lean_dec(v___x_3320_);
v___y_3337_ = v___y_3400_;
v___y_3338_ = v___y_3404_;
v___y_3339_ = v___y_3406_;
v___y_3340_ = v___x_3411_;
v___y_3341_ = v___y_3408_;
v___y_3342_ = v___y_3403_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3407_;
goto v___jp_3336_;
}
else
{
lean_object* v_inheritedTraceOptions_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v_inheritedTraceOptions_3417_ = lean_ctor_get(v_toCold_3414_, 11);
v___x_3418_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3419_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3420_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3415_, v___x_3419_);
if (v___x_3420_ == 0)
{
lean_dec(v___y_3409_);
lean_dec(v___x_3320_);
v___y_3337_ = v___y_3400_;
v___y_3338_ = v___y_3404_;
v___y_3339_ = v___y_3406_;
v___y_3340_ = v___x_3411_;
v___y_3341_ = v___y_3408_;
v___y_3342_ = v___y_3403_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3407_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3421_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3422_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3406_);
v___x_3423_ = l_Lean_inlineExpr(v___y_3406_, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3421_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_nat_dec_eq(v___y_3409_, v___x_3320_);
lean_dec(v___x_3320_);
lean_dec(v___y_3409_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3426_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3400_);
v___x_3427_ = lean_array_to_list(v___y_3400_);
v___x_3428_ = lean_box(0);
v___x_3429_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3427_, v___x_3428_);
v___x_3430_ = l_Lean_MessageData_ofList(v___x_3429_);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3426_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___y_3378_ = v___y_3400_;
v___y_3379_ = v___y_3402_;
v___y_3380_ = v___y_3403_;
v___y_3381_ = v___y_3404_;
v___y_3382_ = v___x_3424_;
v___y_3383_ = v___x_3411_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
v___y_3386_ = v___y_3408_;
v___y_3387_ = v___x_3418_;
v___y_3388_ = v___x_3433_;
goto v___jp_3377_;
}
else
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3378_ = v___y_3400_;
v___y_3379_ = v___y_3402_;
v___y_3380_ = v___y_3403_;
v___y_3381_ = v___y_3404_;
v___y_3382_ = v___x_3424_;
v___y_3383_ = v___x_3411_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
v___y_3386_ = v___y_3408_;
v___y_3387_ = v___x_3418_;
v___y_3388_ = v___x_3434_;
goto v___jp_3377_;
}
}
}
}
}
v___jp_3435_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_box(1);
lean_inc_ref(v___y_3441_);
v___x_3445_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3444_, v_localInst2Index_3326_, v___y_3441_);
v___x_3446_ = lean_array_get_size(v___y_3443_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_size_3447_; 
v_size_3447_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_size_3447_);
v___y_3400_ = v___y_3443_;
v___y_3401_ = v___y_3436_;
v___y_3402_ = v___y_3438_;
v___y_3403_ = v___y_3437_;
v___y_3404_ = v___x_3445_;
v___y_3405_ = v___y_3439_;
v___y_3406_ = v___y_3441_;
v___y_3407_ = v___y_3440_;
v___y_3408_ = v___y_3442_;
v___y_3409_ = v___x_3446_;
v___y_3410_ = v_size_3447_;
goto v___jp_3399_;
}
else
{
lean_inc(v___x_3320_);
v___y_3400_ = v___y_3443_;
v___y_3401_ = v___y_3436_;
v___y_3402_ = v___y_3438_;
v___y_3403_ = v___y_3437_;
v___y_3404_ = v___x_3445_;
v___y_3405_ = v___y_3439_;
v___y_3406_ = v___y_3441_;
v___y_3407_ = v___y_3440_;
v___y_3408_ = v___y_3442_;
v___y_3409_ = v___x_3446_;
v___y_3410_ = v___x_3320_;
goto v___jp_3399_;
}
}
v___jp_3448_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3456_ = lean_array_get_size(v_insts_3325_);
v___x_3457_ = lean_mk_empty_array_with_capacity(v___x_3320_);
v___x_3458_ = lean_nat_dec_lt(v___x_3320_, v___x_3456_);
if (v___x_3458_ == 0)
{
lean_dec(v___x_3321_);
v___y_3436_ = v___y_3450_;
v___y_3437_ = v___y_3453_;
v___y_3438_ = v___y_3454_;
v___y_3439_ = v___y_3451_;
v___y_3440_ = v___y_3455_;
v___y_3441_ = v___y_3449_;
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___x_3457_;
goto v___jp_3435_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v_visitedExpr_3463_; size_t v___x_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3459_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
lean_inc(v___x_3320_);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3320_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
lean_inc_ref(v___x_3457_);
v___x_3461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v___x_3321_);
lean_ctor_set(v___x_3461_, 2, v___x_3457_);
lean_inc_ref(v___y_3449_);
v___x_3462_ = l_Lean_collectFVars(v___x_3461_, v___y_3449_);
v_visitedExpr_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc_ref(v_visitedExpr_3463_);
lean_dec_ref(v___x_3462_);
v___x_3464_ = ((size_t)0ULL);
v___x_3465_ = lean_usize_of_nat(v___x_3456_);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3463_, v_insts_3325_, v___x_3464_, v___x_3465_, v___x_3457_);
lean_dec_ref(v_visitedExpr_3463_);
v___y_3436_ = v___y_3450_;
v___y_3437_ = v___y_3453_;
v___y_3438_ = v___y_3454_;
v___y_3439_ = v___y_3451_;
v___y_3440_ = v___y_3455_;
v___y_3441_ = v___y_3449_;
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___x_3466_;
goto v___jp_3435_;
}
}
v___jp_3467_:
{
lean_object* v___x_3469_; 
lean_inc_ref(v_val_3468_);
v___x_3469_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3468_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v___x_3470_; lean_object* v_a_3471_; uint8_t v___x_3472_; 
lean_dec_ref_known(v___x_3469_, 1);
v___x_3470_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3468_, v___y_3330_);
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = l_Lean_Expr_hasMVar(v_a_3471_);
if (v___x_3472_ == 0)
{
v___y_3449_ = v_a_3471_;
v___y_3450_ = v___y_3327_;
v___y_3451_ = v___y_3328_;
v___y_3452_ = v___y_3329_;
v___y_3453_ = v___y_3330_;
v___y_3454_ = v___y_3331_;
v___y_3455_ = v___y_3332_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v___x_3473_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13);
v___x_3474_ = lean_unsigned_to_nat(30u);
v___x_3475_ = l_Lean_inlineExprTrailing(v_a_3471_, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3473_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3476_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v_val_3468_);
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3486_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3469_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3469_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
v___jp_3494_:
{
if (lean_obj_tag(v___y_3495_) == 0)
{
lean_object* v_a_3496_; 
v_a_3496_ = lean_ctor_get(v___y_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___y_3495_, 1);
v_val_3468_ = v_a_3496_;
goto v___jp_3467_;
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3497_ = lean_ctor_get(v___y_3495_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___y_3495_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___y_3495_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___y_3495_);
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
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_3505_:
{
if (lean_obj_tag(v___y_3506_) == 0)
{
lean_object* v_a_3507_; 
v_a_3507_ = lean_ctor_get(v___y_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v___y_3506_, 1);
v_val_3468_ = v_a_3507_;
goto v___jp_3467_;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_type_3335_);
lean_dec(v_localInst2Index_3326_);
lean_dec(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_xs_3319_);
v_a_3508_ = lean_ctor_get(v___y_3506_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___y_3506_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___y_3506_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___y_3506_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_3933_ = _args[0];
lean_object* v_us_3934_ = _args[1];
lean_object* v_xs_3935_ = _args[2];
lean_object* v___x_3936_ = _args[3];
lean_object* v___x_3937_ = _args[4];
lean_object* v_ctorName_3938_ = _args[5];
lean_object* v___x_3939_ = _args[6];
lean_object* v___f_3940_ = _args[7];
lean_object* v_insts_3941_ = _args[8];
lean_object* v_localInst2Index_3942_ = _args[9];
lean_object* v___y_3943_ = _args[10];
lean_object* v___y_3944_ = _args[11];
lean_object* v___y_3945_ = _args[12];
lean_object* v___y_3946_ = _args[13];
lean_object* v___y_3947_ = _args[14];
lean_object* v___y_3948_ = _args[15];
lean_object* v___y_3949_ = _args[16];
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_3933_, v_us_3934_, v_xs_3935_, v___x_3936_, v___x_3937_, v_ctorName_3938_, v___x_3939_, v___f_3940_, v_insts_3941_, v_localInst2Index_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec_ref(v_insts_3941_);
lean_dec_ref(v___x_3939_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_3951_, size_t v_i_3952_, lean_object* v_bs_3953_){
_start:
{
uint8_t v___x_3954_; 
v___x_3954_ = lean_usize_dec_lt(v_i_3952_, v_sz_3951_);
if (v___x_3954_ == 0)
{
return v_bs_3953_;
}
else
{
lean_object* v_v_3955_; lean_object* v___x_3956_; lean_object* v_bs_x27_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; size_t v___x_3962_; size_t v___x_3963_; lean_object* v___x_3964_; 
v_v_3955_ = lean_array_uget(v_bs_3953_, v_i_3952_);
v___x_3956_ = lean_unsigned_to_nat(0u);
v_bs_x27_3957_ = lean_array_uset(v_bs_3953_, v_i_3952_, v___x_3956_);
v___x_3958_ = l_Lean_Expr_fvarId_x21(v_v_3955_);
lean_dec(v_v_3955_);
v___x_3959_ = 1;
v___x_3960_ = lean_box(v___x_3959_);
v___x_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3958_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = ((size_t)1ULL);
v___x_3963_ = lean_usize_add(v_i_3952_, v___x_3962_);
v___x_3964_ = lean_array_uset(v_bs_x27_3957_, v_i_3952_, v___x_3961_);
v_i_3952_ = v___x_3963_;
v_bs_3953_ = v___x_3964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_3966_, lean_object* v_i_3967_, lean_object* v_bs_3968_){
_start:
{
size_t v_sz_boxed_3969_; size_t v_i_boxed_3970_; lean_object* v_res_3971_; 
v_sz_boxed_3969_ = lean_unbox_usize(v_sz_3966_);
lean_dec(v_sz_3966_);
v_i_boxed_3970_ = lean_unbox_usize(v_i_3967_);
lean_dec(v_i_3967_);
v_res_3971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_3969_, v_i_boxed_3970_, v_bs_3968_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
lean_inc(v___y_3974_);
lean_inc_ref(v___y_3973_);
v___x_3980_ = lean_apply_7(v_k_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, lean_box(0));
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_3990_, lean_object* v_k_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___f_3999_; lean_object* v___x_4000_; 
lean_inc(v___y_3993_);
lean_inc_ref(v___y_3992_);
v___f_3999_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3999_, 0, v_k_3991_);
lean_closure_set(v___f_3999_, 1, v___y_3992_);
lean_closure_set(v___f_3999_, 2, v___y_3993_);
v___x_4000_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3990_, v___f_3999_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
if (lean_obj_tag(v___x_4000_) == 0)
{
return v___x_4000_;
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_4000_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_4000_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4009_, lean_object* v_k_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4009_, v_k_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec_ref(v_bs_4009_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4019_, lean_object* v_k_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
size_t v_sz_4028_; size_t v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_sz_4028_ = lean_array_size(v_bs_4019_);
v___x_4029_ = ((size_t)0ULL);
v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4028_, v___x_4029_, v_bs_4019_);
v___x_4031_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4030_, v_k_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec_ref(v___x_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4032_, lean_object* v_k_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4032_, v_k_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4042_, lean_object* v_inductiveTypeName_4043_, lean_object* v_us_4044_, lean_object* v___x_4045_, lean_object* v_ctorName_4046_, lean_object* v___f_4047_, uint8_t v_addHypotheses_4048_, lean_object* v_xs_4049_, lean_object* v_x_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___f_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4058_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4049_, 2);
v___x_4059_ = l_Array_toSubarray___redArg(v_xs_4049_, v___x_4058_, v_numParams_4042_);
v___x_4060_ = l_Subarray_copy___redArg(v___x_4059_);
lean_inc_ref(v___x_4060_);
v___f_4061_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4061_, 0, v_inductiveTypeName_4043_);
lean_closure_set(v___f_4061_, 1, v_us_4044_);
lean_closure_set(v___f_4061_, 2, v_xs_4049_);
lean_closure_set(v___f_4061_, 3, v___x_4058_);
lean_closure_set(v___f_4061_, 4, v___x_4045_);
lean_closure_set(v___f_4061_, 5, v_ctorName_4046_);
lean_closure_set(v___f_4061_, 6, v___x_4060_);
lean_closure_set(v___f_4061_, 7, v___f_4047_);
v___x_4062_ = lean_box(v_addHypotheses_4048_);
v___x_4063_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4063_, 0, v___x_4062_);
lean_closure_set(v___x_4063_, 1, lean_box(0));
lean_closure_set(v___x_4063_, 2, v___x_4060_);
lean_closure_set(v___x_4063_, 3, v___f_4061_);
v___x_4064_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4049_, v___x_4063_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4065_, lean_object* v_inductiveTypeName_4066_, lean_object* v_us_4067_, lean_object* v___x_4068_, lean_object* v_ctorName_4069_, lean_object* v___f_4070_, lean_object* v_addHypotheses_4071_, lean_object* v_xs_4072_, lean_object* v_x_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
uint8_t v_addHypotheses_boxed_4081_; lean_object* v_res_4082_; 
v_addHypotheses_boxed_4081_ = lean_unbox(v_addHypotheses_4071_);
v_res_4082_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4065_, v_inductiveTypeName_4066_, v_us_4067_, v___x_4068_, v_ctorName_4069_, v___f_4070_, v_addHypotheses_boxed_4081_, v_xs_4072_, v_x_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec_ref(v_x_4073_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
if (lean_obj_tag(v_a_4083_) == 0)
{
lean_object* v___x_4085_; 
v___x_4085_ = l_List_reverse___redArg(v_a_4084_);
return v___x_4085_;
}
else
{
lean_object* v_head_4086_; lean_object* v_tail_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4096_; 
v_head_4086_ = lean_ctor_get(v_a_4083_, 0);
v_tail_4087_ = lean_ctor_get(v_a_4083_, 1);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_a_4083_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4089_ = v_a_4083_;
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_tail_4087_);
lean_inc(v_head_4086_);
lean_dec(v_a_4083_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4091_ = l_Lean_Level_param___override(v_head_4086_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 1, v_a_4084_);
lean_ctor_set(v___x_4089_, 0, v___x_4091_);
v___x_4093_ = v___x_4089_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4091_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_a_4084_);
v___x_4093_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
v_a_4083_ = v_tail_4087_;
v_a_4084_ = v___x_4093_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4098_, lean_object* v_ctorName_4099_, uint8_t v_addHypotheses_4100_, lean_object* v_indVal_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_toConstantVal_4109_; lean_object* v_numParams_4110_; lean_object* v_levelParams_4111_; lean_object* v_type_4112_; lean_object* v___f_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v_us_4116_; lean_object* v___x_4117_; lean_object* v___f_4118_; uint8_t v___x_4119_; lean_object* v___x_4120_; 
v_toConstantVal_4109_ = lean_ctor_get(v_indVal_4101_, 0);
lean_inc_ref(v_toConstantVal_4109_);
v_numParams_4110_ = lean_ctor_get(v_indVal_4101_, 1);
lean_inc(v_numParams_4110_);
lean_dec_ref(v_indVal_4101_);
v_levelParams_4111_ = lean_ctor_get(v_toConstantVal_4109_, 1);
lean_inc(v_levelParams_4111_);
v_type_4112_ = lean_ctor_get(v_toConstantVal_4109_, 2);
lean_inc_ref(v_type_4112_);
lean_dec_ref(v_toConstantVal_4109_);
v___f_4113_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4114_ = lean_box(1);
v___x_4115_ = lean_box(0);
v_us_4116_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4111_, v___x_4115_);
v___x_4117_ = lean_box(v_addHypotheses_4100_);
v___f_4118_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4118_, 0, v_numParams_4110_);
lean_closure_set(v___f_4118_, 1, v_inductiveTypeName_4098_);
lean_closure_set(v___f_4118_, 2, v_us_4116_);
lean_closure_set(v___f_4118_, 3, v___x_4114_);
lean_closure_set(v___f_4118_, 4, v_ctorName_4099_);
lean_closure_set(v___f_4118_, 5, v___f_4113_);
lean_closure_set(v___f_4118_, 6, v___x_4117_);
v___x_4119_ = 0;
v___x_4120_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4112_, v___f_4118_, v___x_4119_, v___x_4119_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4121_, lean_object* v_ctorName_4122_, lean_object* v_addHypotheses_4123_, lean_object* v_indVal_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
uint8_t v_addHypotheses_boxed_4132_; lean_object* v_res_4133_; 
v_addHypotheses_boxed_4132_ = lean_unbox(v_addHypotheses_4123_);
v_res_4133_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4121_, v_ctorName_4122_, v_addHypotheses_boxed_4132_, v_indVal_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4134_, lean_object* v_bs_4135_, lean_object* v_k_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4135_, v_k_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4145_, lean_object* v_bs_4146_, lean_object* v_k_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4145_, v_bs_4146_, v_k_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec_ref(v_bs_4146_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4156_, lean_object* v_bs_4157_, lean_object* v_k_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4157_, v_k_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4167_, lean_object* v_bs_4168_, lean_object* v_k_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4167_, v_bs_4168_, v_k_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4178_, lean_object* v_levelParams_4179_, lean_object* v_type_4180_, lean_object* v_value_4181_, lean_object* v_hints_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v___x_4185_; uint8_t v___y_4187_; lean_object* v_env_4195_; uint8_t v___x_4196_; 
v___x_4185_ = lean_st_ref_get(v___y_4183_);
v_env_4195_ = lean_ctor_get(v___x_4185_, 0);
lean_inc_ref_n(v_env_4195_, 2);
lean_dec(v___x_4185_);
v___x_4196_ = l_Lean_Environment_hasUnsafe(v_env_4195_, v_type_4180_);
if (v___x_4196_ == 0)
{
uint8_t v___x_4197_; 
v___x_4197_ = l_Lean_Environment_hasUnsafe(v_env_4195_, v_value_4181_);
if (v___x_4197_ == 0)
{
uint8_t v___x_4198_; 
v___x_4198_ = 1;
v___y_4187_ = v___x_4198_;
goto v___jp_4186_;
}
else
{
goto v___jp_4193_;
}
}
else
{
lean_dec_ref(v_env_4195_);
goto v___jp_4193_;
}
v___jp_4186_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_inc(v_name_4178_);
v___x_4188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4188_, 0, v_name_4178_);
lean_ctor_set(v___x_4188_, 1, v_levelParams_4179_);
lean_ctor_set(v___x_4188_, 2, v_type_4180_);
v___x_4189_ = lean_box(0);
v___x_4190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4190_, 0, v_name_4178_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4191_, 0, v___x_4188_);
lean_ctor_set(v___x_4191_, 1, v_value_4181_);
lean_ctor_set(v___x_4191_, 2, v_hints_4182_);
lean_ctor_set(v___x_4191_, 3, v___x_4190_);
lean_ctor_set_uint8(v___x_4191_, sizeof(void*)*4, v___y_4187_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
v___jp_4193_:
{
uint8_t v___x_4194_; 
v___x_4194_ = 0;
v___y_4187_ = v___x_4194_;
goto v___jp_4186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4199_, lean_object* v_levelParams_4200_, lean_object* v_type_4201_, lean_object* v_value_4202_, lean_object* v_hints_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4199_, v_levelParams_4200_, v_type_4201_, v_value_4202_, v_hints_4203_, v___y_4204_);
lean_dec(v___y_4204_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4207_, lean_object* v_levelParams_4208_, lean_object* v_type_4209_, lean_object* v_value_4210_, lean_object* v_hints_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4207_, v_levelParams_4208_, v_type_4209_, v_value_4210_, v_hints_4211_, v___y_4217_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4220_, lean_object* v_levelParams_4221_, lean_object* v_type_4222_, lean_object* v_value_4223_, lean_object* v_hints_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4220_, v_levelParams_4221_, v_type_4222_, v_value_4223_, v_hints_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4233_, uint8_t v_isExporting_4234_, lean_object* v___x_4235_, lean_object* v___y_4236_, lean_object* v___x_4237_, lean_object* v_a_x3f_4238_){
_start:
{
lean_object* v___x_4240_; lean_object* v_env_4241_; lean_object* v_nextMacroScope_4242_; lean_object* v_ngen_4243_; lean_object* v_auxDeclNGen_4244_; lean_object* v_traceState_4245_; lean_object* v_recordedDeps_4246_; lean_object* v_messages_4247_; lean_object* v_infoState_4248_; lean_object* v_snapshotTasks_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4274_; 
v___x_4240_ = lean_st_ref_take(v___y_4233_);
v_env_4241_ = lean_ctor_get(v___x_4240_, 0);
v_nextMacroScope_4242_ = lean_ctor_get(v___x_4240_, 1);
v_ngen_4243_ = lean_ctor_get(v___x_4240_, 2);
v_auxDeclNGen_4244_ = lean_ctor_get(v___x_4240_, 3);
v_traceState_4245_ = lean_ctor_get(v___x_4240_, 4);
v_recordedDeps_4246_ = lean_ctor_get(v___x_4240_, 6);
v_messages_4247_ = lean_ctor_get(v___x_4240_, 7);
v_infoState_4248_ = lean_ctor_get(v___x_4240_, 8);
v_snapshotTasks_4249_ = lean_ctor_get(v___x_4240_, 9);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; 
v_unused_4275_ = lean_ctor_get(v___x_4240_, 5);
lean_dec(v_unused_4275_);
v___x_4251_ = v___x_4240_;
v_isShared_4252_ = v_isSharedCheck_4274_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_snapshotTasks_4249_);
lean_inc(v_infoState_4248_);
lean_inc(v_messages_4247_);
lean_inc(v_recordedDeps_4246_);
lean_inc(v_traceState_4245_);
lean_inc(v_auxDeclNGen_4244_);
lean_inc(v_ngen_4243_);
lean_inc(v_nextMacroScope_4242_);
lean_inc(v_env_4241_);
lean_dec(v___x_4240_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4274_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4253_; lean_object* v___x_4255_; 
v___x_4253_ = l_Lean_Environment_setExporting(v_env_4241_, v_isExporting_4234_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 5, v___x_4235_);
lean_ctor_set(v___x_4251_, 0, v___x_4253_);
v___x_4255_ = v___x_4251_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_nextMacroScope_4242_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_ngen_4243_);
lean_ctor_set(v_reuseFailAlloc_4273_, 3, v_auxDeclNGen_4244_);
lean_ctor_set(v_reuseFailAlloc_4273_, 4, v_traceState_4245_);
lean_ctor_set(v_reuseFailAlloc_4273_, 5, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4273_, 6, v_recordedDeps_4246_);
lean_ctor_set(v_reuseFailAlloc_4273_, 7, v_messages_4247_);
lean_ctor_set(v_reuseFailAlloc_4273_, 8, v_infoState_4248_);
lean_ctor_set(v_reuseFailAlloc_4273_, 9, v_snapshotTasks_4249_);
v___x_4255_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v_mctx_4258_; lean_object* v_zetaDeltaFVarIds_4259_; lean_object* v_postponed_4260_; lean_object* v_diag_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4271_; 
v___x_4256_ = lean_st_ref_put(v___y_4233_, v___x_4255_);
v___x_4257_ = lean_st_ref_take(v___y_4236_);
v_mctx_4258_ = lean_ctor_get(v___x_4257_, 0);
v_zetaDeltaFVarIds_4259_ = lean_ctor_get(v___x_4257_, 2);
v_postponed_4260_ = lean_ctor_get(v___x_4257_, 3);
v_diag_4261_ = lean_ctor_get(v___x_4257_, 4);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4271_ == 0)
{
lean_object* v_unused_4272_; 
v_unused_4272_ = lean_ctor_get(v___x_4257_, 1);
lean_dec(v_unused_4272_);
v___x_4263_ = v___x_4257_;
v_isShared_4264_ = v_isSharedCheck_4271_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_diag_4261_);
lean_inc(v_postponed_4260_);
lean_inc(v_zetaDeltaFVarIds_4259_);
lean_inc(v_mctx_4258_);
lean_dec(v___x_4257_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4271_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4265_; lean_object* v___x_4267_; 
v___x_4265_ = lean_box(0);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 1, v___x_4237_);
v___x_4267_ = v___x_4263_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_mctx_4258_);
lean_ctor_set(v_reuseFailAlloc_4270_, 1, v___x_4237_);
lean_ctor_set(v_reuseFailAlloc_4270_, 2, v_zetaDeltaFVarIds_4259_);
lean_ctor_set(v_reuseFailAlloc_4270_, 3, v_postponed_4260_);
lean_ctor_set(v_reuseFailAlloc_4270_, 4, v_diag_4261_);
v___x_4267_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_st_ref_put(v___y_4236_, v___x_4267_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4265_);
return v___x_4269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4276_, lean_object* v_isExporting_4277_, lean_object* v___x_4278_, lean_object* v___y_4279_, lean_object* v___x_4280_, lean_object* v_a_x3f_4281_, lean_object* v___y_4282_){
_start:
{
uint8_t v_isExporting_boxed_4283_; lean_object* v_res_4284_; 
v_isExporting_boxed_4283_ = lean_unbox(v_isExporting_4277_);
v_res_4284_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4276_, v_isExporting_boxed_4283_, v___x_4278_, v___y_4279_, v___x_4280_, v_a_x3f_4281_);
lean_dec(v_a_x3f_4281_);
lean_dec(v___y_4279_);
lean_dec(v___y_4276_);
return v_res_4284_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4285_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4288_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
return v___x_4289_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4290_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
lean_ctor_set(v___x_4291_, 2, v___x_4290_);
lean_ctor_set(v___x_4291_, 3, v___x_4290_);
lean_ctor_set(v___x_4291_, 4, v___x_4290_);
lean_ctor_set(v___x_4291_, 5, v___x_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4292_, uint8_t v_isExporting_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; lean_object* v_env_4302_; lean_object* v___x_4303_; uint8_t v_isModule_4304_; 
v___x_4301_ = lean_st_ref_get(v___y_4299_);
v_env_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc_ref(v_env_4302_);
lean_dec(v___x_4301_);
v___x_4303_ = l_Lean_Environment_header(v_env_4302_);
v_isModule_4304_ = lean_ctor_get_uint8(v___x_4303_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4303_);
if (v_isModule_4304_ == 0)
{
lean_object* v___x_4305_; 
lean_dec_ref(v_env_4302_);
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
v___x_4305_ = lean_apply_7(v_x_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
return v___x_4305_;
}
else
{
uint8_t v_isExporting_4306_; 
v_isExporting_4306_ = lean_ctor_get_uint8(v_env_4302_, sizeof(void*)*13);
lean_dec_ref(v_env_4302_);
if (v_isExporting_4293_ == 0)
{
if (v_isExporting_4306_ == 0)
{
lean_object* v___x_4373_; 
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
v___x_4373_ = lean_apply_7(v_x_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
return v___x_4373_;
}
else
{
goto v___jp_4307_;
}
}
else
{
if (v_isExporting_4306_ == 0)
{
goto v___jp_4307_;
}
else
{
lean_object* v___x_4374_; 
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
v___x_4374_ = lean_apply_7(v_x_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
return v___x_4374_;
}
}
v___jp_4307_:
{
lean_object* v___x_4308_; lean_object* v_env_4309_; lean_object* v_nextMacroScope_4310_; lean_object* v_ngen_4311_; lean_object* v_auxDeclNGen_4312_; lean_object* v_traceState_4313_; lean_object* v_recordedDeps_4314_; lean_object* v_messages_4315_; lean_object* v_infoState_4316_; lean_object* v_snapshotTasks_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4371_; 
v___x_4308_ = lean_st_ref_take(v___y_4299_);
v_env_4309_ = lean_ctor_get(v___x_4308_, 0);
v_nextMacroScope_4310_ = lean_ctor_get(v___x_4308_, 1);
v_ngen_4311_ = lean_ctor_get(v___x_4308_, 2);
v_auxDeclNGen_4312_ = lean_ctor_get(v___x_4308_, 3);
v_traceState_4313_ = lean_ctor_get(v___x_4308_, 4);
v_recordedDeps_4314_ = lean_ctor_get(v___x_4308_, 6);
v_messages_4315_ = lean_ctor_get(v___x_4308_, 7);
v_infoState_4316_ = lean_ctor_get(v___x_4308_, 8);
v_snapshotTasks_4317_ = lean_ctor_get(v___x_4308_, 9);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4371_ == 0)
{
lean_object* v_unused_4372_; 
v_unused_4372_ = lean_ctor_get(v___x_4308_, 5);
lean_dec(v_unused_4372_);
v___x_4319_ = v___x_4308_;
v_isShared_4320_ = v_isSharedCheck_4371_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_snapshotTasks_4317_);
lean_inc(v_infoState_4316_);
lean_inc(v_messages_4315_);
lean_inc(v_recordedDeps_4314_);
lean_inc(v_traceState_4313_);
lean_inc(v_auxDeclNGen_4312_);
lean_inc(v_ngen_4311_);
lean_inc(v_nextMacroScope_4310_);
lean_inc(v_env_4309_);
lean_dec(v___x_4308_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4371_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4324_; 
v___x_4321_ = l_Lean_Environment_setExporting(v_env_4309_, v_isExporting_4293_);
v___x_4322_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 5, v___x_4322_);
lean_ctor_set(v___x_4319_, 0, v___x_4321_);
v___x_4324_ = v___x_4319_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4321_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_nextMacroScope_4310_);
lean_ctor_set(v_reuseFailAlloc_4370_, 2, v_ngen_4311_);
lean_ctor_set(v_reuseFailAlloc_4370_, 3, v_auxDeclNGen_4312_);
lean_ctor_set(v_reuseFailAlloc_4370_, 4, v_traceState_4313_);
lean_ctor_set(v_reuseFailAlloc_4370_, 5, v___x_4322_);
lean_ctor_set(v_reuseFailAlloc_4370_, 6, v_recordedDeps_4314_);
lean_ctor_set(v_reuseFailAlloc_4370_, 7, v_messages_4315_);
lean_ctor_set(v_reuseFailAlloc_4370_, 8, v_infoState_4316_);
lean_ctor_set(v_reuseFailAlloc_4370_, 9, v_snapshotTasks_4317_);
v___x_4324_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v_mctx_4327_; lean_object* v_zetaDeltaFVarIds_4328_; lean_object* v_postponed_4329_; lean_object* v_diag_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4368_; 
v___x_4325_ = lean_st_ref_put(v___y_4299_, v___x_4324_);
v___x_4326_ = lean_st_ref_take(v___y_4297_);
v_mctx_4327_ = lean_ctor_get(v___x_4326_, 0);
v_zetaDeltaFVarIds_4328_ = lean_ctor_get(v___x_4326_, 2);
v_postponed_4329_ = lean_ctor_get(v___x_4326_, 3);
v_diag_4330_ = lean_ctor_get(v___x_4326_, 4);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4368_ == 0)
{
lean_object* v_unused_4369_; 
v_unused_4369_ = lean_ctor_get(v___x_4326_, 1);
lean_dec(v_unused_4369_);
v___x_4332_ = v___x_4326_;
v_isShared_4333_ = v_isSharedCheck_4368_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_diag_4330_);
lean_inc(v_postponed_4329_);
lean_inc(v_zetaDeltaFVarIds_4328_);
lean_inc(v_mctx_4327_);
lean_dec(v___x_4326_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4368_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4334_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 1, v___x_4334_);
v___x_4336_ = v___x_4332_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_mctx_4327_);
lean_ctor_set(v_reuseFailAlloc_4367_, 1, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4367_, 2, v_zetaDeltaFVarIds_4328_);
lean_ctor_set(v_reuseFailAlloc_4367_, 3, v_postponed_4329_);
lean_ctor_set(v_reuseFailAlloc_4367_, 4, v_diag_4330_);
v___x_4336_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4337_; lean_object* v_r_4338_; 
v___x_4337_ = lean_st_ref_put(v___y_4297_, v___x_4336_);
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
v_r_4338_ = lean_apply_7(v_x_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
if (lean_obj_tag(v_r_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4355_; 
v_a_4339_ = lean_ctor_get(v_r_4338_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_r_4338_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4341_ = v_r_4338_;
v_isShared_4342_ = v_isSharedCheck_4355_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v_r_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4355_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
lean_inc(v_a_4339_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set_tag(v___x_4341_, 1);
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
v___x_4345_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4299_, v_isExporting_4306_, v___x_4322_, v___y_4297_, v___x_4334_, v___x_4344_);
lean_dec_ref(v___x_4344_);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4352_ == 0)
{
lean_object* v_unused_4353_; 
v_unused_4353_ = lean_ctor_get(v___x_4345_, 0);
lean_dec(v_unused_4353_);
v___x_4347_ = v___x_4345_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_dec(v___x_4345_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v_a_4339_);
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_a_4339_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
v_a_4356_ = lean_ctor_get(v_r_4338_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v_r_4338_, 1);
v___x_4357_ = lean_box(0);
v___x_4358_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4299_, v_isExporting_4306_, v___x_4322_, v___y_4297_, v___x_4334_, v___x_4357_);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; 
v_unused_4366_ = lean_ctor_get(v___x_4358_, 0);
lean_dec(v_unused_4366_);
v___x_4360_ = v___x_4358_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_dec(v___x_4358_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
lean_ctor_set_tag(v___x_4360_, 1);
lean_ctor_set(v___x_4360_, 0, v_a_4356_);
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4356_);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4375_, lean_object* v_isExporting_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
uint8_t v_isExporting_boxed_4384_; lean_object* v_res_4385_; 
v_isExporting_boxed_4384_ = lean_unbox(v_isExporting_4376_);
v_res_4385_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4375_, v_isExporting_boxed_4384_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4386_, lean_object* v_x_4387_, uint8_t v_isExporting_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4387_, v_isExporting_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4397_, lean_object* v_x_4398_, lean_object* v_isExporting_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
uint8_t v_isExporting_boxed_4407_; lean_object* v_res_4408_; 
v_isExporting_boxed_4407_ = lean_unbox(v_isExporting_4399_);
v_res_4408_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4397_, v_x_4398_, v_isExporting_boxed_4407_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4419_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
return v_res_4429_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4432_ = l_Lean_stringToMessageData(v___x_4431_);
return v___x_4432_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4435_ = l_Lean_stringToMessageData(v___x_4434_);
return v___x_4435_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4438_ = l_Lean_stringToMessageData(v___x_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4439_, lean_object* v___x_4440_, lean_object* v_inductiveTypeName_4441_, uint8_t v___x_4442_, lean_object* v___x_4443_, lean_object* v___f_4444_, lean_object* v_ctorName_4445_, uint8_t v_addHypotheses_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v___y_4455_; lean_object* v___x_4458_; 
lean_inc(v_inductiveTypeName_4441_);
v___x_4458_ = l_Lean_Elab_Deriving_mkContext(v___x_4439_, v___x_4440_, v_inductiveTypeName_4441_, v___x_4442_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_toCold_4459_; lean_object* v_a_4460_; lean_object* v_options_4461_; lean_object* v_currNamespace_4462_; lean_object* v_inheritedTraceOptions_4463_; lean_object* v_instName_4464_; lean_object* v_auxFunNames_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4511_; uint8_t v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; uint8_t v___y_4520_; lean_object* v___y_4559_; uint8_t v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___x_4574_; 
v_toCold_4459_ = lean_ctor_get(v___y_4451_, 0);
v_a_4460_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4458_, 1);
v_options_4461_ = lean_ctor_get(v_toCold_4459_, 2);
v_currNamespace_4462_ = lean_ctor_get(v_toCold_4459_, 4);
v_inheritedTraceOptions_4463_ = lean_ctor_get(v_toCold_4459_, 11);
v_instName_4464_ = lean_ctor_get(v_a_4460_, 0);
lean_inc(v_instName_4464_);
v_auxFunNames_4465_ = lean_ctor_get(v_a_4460_, 2);
lean_inc_ref(v_auxFunNames_4465_);
lean_dec(v_a_4460_);
v___x_4466_ = lean_unsigned_to_nat(0u);
v___x_4467_ = lean_array_get(v___x_4443_, v_auxFunNames_4465_, v___x_4466_);
lean_dec_ref(v_auxFunNames_4465_);
lean_inc(v_currNamespace_4462_);
v___x_4468_ = l_Lean_Name_append(v_currNamespace_4462_, v___x_4467_);
lean_inc(v_inductiveTypeName_4441_);
v___x_4574_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4441_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v_a_4577_; lean_object* v___y_4649_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc_n(v_a_4575_, 2);
lean_dec_ref_known(v___x_4574_, 1);
v___x_4671_ = lean_box(v_addHypotheses_4446_);
lean_inc(v_inductiveTypeName_4441_);
v___x_4672_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4672_, 0, v_inductiveTypeName_4441_);
lean_closure_set(v___x_4672_, 1, v_ctorName_4445_);
lean_closure_set(v___x_4672_, 2, v___x_4671_);
lean_closure_set(v___x_4672_, 3, v_a_4575_);
lean_inc(v___x_4468_);
v___x_4673_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4468_, v___x_4672_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; 
lean_dec_ref(v___f_4444_);
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v_a_4577_ = v_a_4674_;
goto v___jp_4576_;
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4705_; 
v_a_4675_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4677_ = v___x_4673_;
v_isShared_4678_ = v_isSharedCheck_4705_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4673_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4705_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
uint8_t v___x_4679_; 
v___x_4679_ = l_Lean_Exception_isInterrupt(v_a_4675_);
if (v___x_4679_ == 0)
{
uint8_t v___x_4680_; 
lean_inc(v_a_4675_);
v___x_4680_ = l_Lean_Exception_isRuntime(v_a_4675_);
if (v___x_4680_ == 0)
{
uint8_t v_hasTrace_4681_; 
lean_del_object(v___x_4677_);
v_hasTrace_4681_ = lean_ctor_get_uint8(v_options_4461_, sizeof(void*)*1);
if (v_hasTrace_4681_ == 0)
{
lean_dec(v_a_4675_);
goto v___jp_4668_;
}
else
{
lean_object* v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; 
v___x_4682_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4683_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4684_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4463_, v_options_4461_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_dec(v_a_4675_);
goto v___jp_4668_;
}
else
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4685_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4686_ = l_Lean_Exception_toMessageData(v_a_4675_);
v___x_4687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4685_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4682_, v___x_4687_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4690_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v___x_4688_, 1);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
lean_inc(v___y_4450_);
lean_inc_ref(v___y_4449_);
lean_inc(v___y_4448_);
lean_inc_ref(v___y_4447_);
v___x_4690_ = lean_apply_8(v___f_4444_, v_a_4689_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, lean_box(0));
v___y_4649_ = v___x_4690_;
goto v___jp_4648_;
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_dec(v_a_4575_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec_ref(v___f_4444_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4691_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4688_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4688_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
}
}
else
{
lean_object* v___x_4700_; 
lean_dec(v_a_4575_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec_ref(v___f_4444_);
lean_dec(v_inductiveTypeName_4441_);
if (v_isShared_4678_ == 0)
{
v___x_4700_ = v___x_4677_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4675_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
else
{
lean_object* v___x_4703_; 
lean_dec(v_a_4575_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec_ref(v___f_4444_);
lean_dec(v_inductiveTypeName_4441_);
if (v_isShared_4678_ == 0)
{
v___x_4703_ = v___x_4677_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4675_);
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
v___jp_4576_:
{
lean_object* v_snd_4578_; lean_object* v_fst_4579_; lean_object* v_fst_4580_; lean_object* v_snd_4581_; lean_object* v___x_4582_; lean_object* v_toConstantVal_4583_; lean_object* v_env_4584_; lean_object* v_levelParams_4585_; uint32_t v___x_4586_; uint32_t v___x_4587_; uint32_t v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4647_; 
v_snd_4578_ = lean_ctor_get(v_a_4577_, 1);
lean_inc(v_snd_4578_);
v_fst_4579_ = lean_ctor_get(v_a_4577_, 0);
lean_inc(v_fst_4579_);
lean_dec_ref(v_a_4577_);
v_fst_4580_ = lean_ctor_get(v_snd_4578_, 0);
lean_inc_n(v_fst_4580_, 2);
v_snd_4581_ = lean_ctor_get(v_snd_4578_, 1);
lean_inc(v_snd_4581_);
lean_dec(v_snd_4578_);
v___x_4582_ = lean_st_ref_get(v___y_4452_);
v_toConstantVal_4583_ = lean_ctor_get(v_a_4575_, 0);
lean_inc_ref(v_toConstantVal_4583_);
lean_dec(v_a_4575_);
v_env_4584_ = lean_ctor_get(v___x_4582_, 0);
lean_inc_ref(v_env_4584_);
lean_dec(v___x_4582_);
v_levelParams_4585_ = lean_ctor_get(v_toConstantVal_4583_, 1);
lean_inc(v_levelParams_4585_);
lean_dec_ref(v_toConstantVal_4583_);
v___x_4586_ = l_Lean_getMaxHeight(v_env_4584_, v_fst_4580_);
v___x_4587_ = 1;
v___x_4588_ = lean_uint32_add(v___x_4586_, v___x_4587_);
v___x_4589_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4589_, 0, v___x_4588_);
lean_inc(v___x_4468_);
v___x_4590_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4468_, v_levelParams_4585_, v_fst_4579_, v_fst_4580_, v___x_4589_, v___y_4452_);
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4593_ = v___x_4590_;
v_isShared_4594_ = v_isSharedCheck_4647_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4590_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4647_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
lean_ctor_set_tag(v___x_4593_, 1);
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
uint8_t v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = 0;
v___x_4598_ = l_Lean_addDecl(v___x_4596_, v___x_4597_, v___y_4451_, v___y_4452_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v___x_4599_; lean_object* v_env_4600_; uint8_t v___x_4601_; 
lean_dec_ref_known(v___x_4598_, 1);
v___x_4599_ = lean_st_ref_get(v___y_4452_);
v_env_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc_ref(v_env_4600_);
lean_dec(v___x_4599_);
lean_inc(v_inductiveTypeName_4441_);
v___x_4601_ = l_Lean_isMarkedMeta(v_env_4600_, v_inductiveTypeName_4441_);
if (v___x_4601_ == 0)
{
v___y_4559_ = v_snd_4581_;
v___y_4560_ = v___x_4597_;
v___y_4561_ = v___y_4447_;
v___y_4562_ = v___y_4448_;
v___y_4563_ = v___y_4449_;
v___y_4564_ = v___y_4450_;
v___y_4565_ = v___y_4451_;
v___y_4566_ = v___y_4452_;
goto v___jp_4558_;
}
else
{
lean_object* v___x_4602_; lean_object* v_env_4603_; lean_object* v_nextMacroScope_4604_; lean_object* v_ngen_4605_; lean_object* v_auxDeclNGen_4606_; lean_object* v_traceState_4607_; lean_object* v_recordedDeps_4608_; lean_object* v_messages_4609_; lean_object* v_infoState_4610_; lean_object* v_snapshotTasks_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4636_; 
v___x_4602_ = lean_st_ref_take(v___y_4452_);
v_env_4603_ = lean_ctor_get(v___x_4602_, 0);
v_nextMacroScope_4604_ = lean_ctor_get(v___x_4602_, 1);
v_ngen_4605_ = lean_ctor_get(v___x_4602_, 2);
v_auxDeclNGen_4606_ = lean_ctor_get(v___x_4602_, 3);
v_traceState_4607_ = lean_ctor_get(v___x_4602_, 4);
v_recordedDeps_4608_ = lean_ctor_get(v___x_4602_, 6);
v_messages_4609_ = lean_ctor_get(v___x_4602_, 7);
v_infoState_4610_ = lean_ctor_get(v___x_4602_, 8);
v_snapshotTasks_4611_ = lean_ctor_get(v___x_4602_, 9);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4636_ == 0)
{
lean_object* v_unused_4637_; 
v_unused_4637_ = lean_ctor_get(v___x_4602_, 5);
lean_dec(v_unused_4637_);
v___x_4613_ = v___x_4602_;
v_isShared_4614_ = v_isSharedCheck_4636_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_snapshotTasks_4611_);
lean_inc(v_infoState_4610_);
lean_inc(v_messages_4609_);
lean_inc(v_recordedDeps_4608_);
lean_inc(v_traceState_4607_);
lean_inc(v_auxDeclNGen_4606_);
lean_inc(v_ngen_4605_);
lean_inc(v_nextMacroScope_4604_);
lean_inc(v_env_4603_);
lean_dec(v___x_4602_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4636_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
lean_inc(v___x_4468_);
v___x_4615_ = l_Lean_markMeta(v_env_4603_, v___x_4468_);
v___x_4616_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 5, v___x_4616_);
lean_ctor_set(v___x_4613_, 0, v___x_4615_);
v___x_4618_ = v___x_4613_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_nextMacroScope_4604_);
lean_ctor_set(v_reuseFailAlloc_4635_, 2, v_ngen_4605_);
lean_ctor_set(v_reuseFailAlloc_4635_, 3, v_auxDeclNGen_4606_);
lean_ctor_set(v_reuseFailAlloc_4635_, 4, v_traceState_4607_);
lean_ctor_set(v_reuseFailAlloc_4635_, 5, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4635_, 6, v_recordedDeps_4608_);
lean_ctor_set(v_reuseFailAlloc_4635_, 7, v_messages_4609_);
lean_ctor_set(v_reuseFailAlloc_4635_, 8, v_infoState_4610_);
lean_ctor_set(v_reuseFailAlloc_4635_, 9, v_snapshotTasks_4611_);
v___x_4618_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v_mctx_4621_; lean_object* v_zetaDeltaFVarIds_4622_; lean_object* v_postponed_4623_; lean_object* v_diag_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4633_; 
v___x_4619_ = lean_st_ref_put(v___y_4452_, v___x_4618_);
v___x_4620_ = lean_st_ref_take(v___y_4450_);
v_mctx_4621_ = lean_ctor_get(v___x_4620_, 0);
v_zetaDeltaFVarIds_4622_ = lean_ctor_get(v___x_4620_, 2);
v_postponed_4623_ = lean_ctor_get(v___x_4620_, 3);
v_diag_4624_ = lean_ctor_get(v___x_4620_, 4);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4633_ == 0)
{
lean_object* v_unused_4634_; 
v_unused_4634_ = lean_ctor_get(v___x_4620_, 1);
lean_dec(v_unused_4634_);
v___x_4626_ = v___x_4620_;
v_isShared_4627_ = v_isSharedCheck_4633_;
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
v_isShared_4627_ = v_isSharedCheck_4633_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4628_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 1, v___x_4628_);
v___x_4630_ = v___x_4626_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_mctx_4621_);
lean_ctor_set(v_reuseFailAlloc_4632_, 1, v___x_4628_);
lean_ctor_set(v_reuseFailAlloc_4632_, 2, v_zetaDeltaFVarIds_4622_);
lean_ctor_set(v_reuseFailAlloc_4632_, 3, v_postponed_4623_);
lean_ctor_set(v_reuseFailAlloc_4632_, 4, v_diag_4624_);
v___x_4630_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_st_ref_put(v___y_4450_, v___x_4630_);
v___y_4559_ = v_snd_4581_;
v___y_4560_ = v___x_4597_;
v___y_4561_ = v___y_4447_;
v___y_4562_ = v___y_4448_;
v___y_4563_ = v___y_4449_;
v___y_4564_ = v___y_4450_;
v___y_4565_ = v___y_4451_;
v___y_4566_ = v___y_4452_;
goto v___jp_4558_;
}
}
}
}
}
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
lean_dec(v_snd_4581_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4638_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4598_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4598_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
}
}
v___jp_4648_:
{
if (lean_obj_tag(v___y_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4659_; 
v_a_4650_ = lean_ctor_get(v___y_4649_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___y_4649_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4652_ = v___y_4649_;
v_isShared_4653_ = v_isSharedCheck_4659_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___y_4649_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4659_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
if (lean_obj_tag(v_a_4650_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4656_; 
lean_dec(v_a_4575_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4654_ = lean_ctor_get(v_a_4650_, 0);
lean_inc(v_a_4654_);
lean_dec_ref_known(v_a_4650_, 1);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v_a_4654_);
v___x_4656_ = v___x_4652_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4654_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
else
{
lean_object* v_a_4658_; 
lean_del_object(v___x_4652_);
v_a_4658_ = lean_ctor_get(v_a_4650_, 0);
lean_inc(v_a_4658_);
lean_dec_ref_known(v_a_4650_, 1);
v_a_4577_ = v_a_4658_;
goto v___jp_4576_;
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec(v_a_4575_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4660_ = lean_ctor_get(v___y_4649_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___y_4649_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___y_4649_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___y_4649_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
v___jp_4668_:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = lean_box(0);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
lean_inc(v___y_4450_);
lean_inc_ref(v___y_4449_);
lean_inc(v___y_4448_);
lean_inc_ref(v___y_4447_);
v___x_4670_ = lean_apply_8(v___f_4444_, v___x_4669_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, lean_box(0));
v___y_4649_ = v___x_4670_;
goto v___jp_4648_;
}
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v_ctorName_4445_);
lean_dec_ref(v___f_4444_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4706_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___x_4574_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4574_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
v___jp_4469_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = l_Lean_mkIdent(v_instName_4464_);
v___x_4479_ = l_Lean_mkCIdent(v___x_4468_);
v___x_4480_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4441_, v___x_4478_, v___y_4470_, v___x_4479_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4470_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_toCold_4481_; lean_object* v_options_4482_; uint8_t v_hasTrace_4483_; 
v_toCold_4481_ = lean_ctor_get(v___y_4476_, 0);
v_options_4482_ = lean_ctor_get(v_toCold_4481_, 2);
v_hasTrace_4483_ = lean_ctor_get_uint8(v_options_4482_, sizeof(void*)*1);
if (v_hasTrace_4483_ == 0)
{
lean_object* v_a_4484_; 
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4471_);
v_a_4484_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4480_, 1);
v___y_4455_ = v_a_4484_;
goto v___jp_4454_;
}
else
{
lean_object* v_a_4485_; lean_object* v_inheritedTraceOptions_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; uint8_t v___x_4489_; 
v_a_4485_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4485_);
lean_dec_ref_known(v___x_4480_, 1);
v_inheritedTraceOptions_4486_ = lean_ctor_get(v_toCold_4481_, 11);
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4471_);
v___x_4488_ = l_Lean_Name_append(v___x_4487_, v___y_4471_);
v___x_4489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4486_, v_options_4482_, v___x_4488_);
lean_dec(v___x_4488_);
if (v___x_4489_ == 0)
{
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4471_);
v___y_4455_ = v_a_4485_;
goto v___jp_4454_;
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4490_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4485_);
v___x_4491_ = l_Lean_MessageData_ofSyntax(v_a_4485_);
v___x_4492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4490_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
v___x_4493_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4471_, v___x_4492_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_dec_ref_known(v___x_4493_, 1);
v___y_4455_ = v_a_4485_;
goto v___jp_4454_;
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_a_4485_);
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4493_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4493_);
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
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4471_);
v_a_4502_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4480_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4480_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
v___jp_4510_:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Lean_compileDecls(v___y_4519_, v___y_4520_, v___y_4514_, v___y_4518_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v___x_4522_; 
lean_dec_ref_known(v___x_4521_, 1);
lean_inc(v___x_4468_);
v___x_4522_ = l_Lean_enableRealizationsForConst(v___x_4468_, v___y_4514_, v___y_4518_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_toCold_4523_; lean_object* v_options_4524_; lean_object* v_inheritedTraceOptions_4525_; uint8_t v_hasTrace_4526_; lean_object* v___x_4527_; 
lean_dec_ref_known(v___x_4522_, 1);
v_toCold_4523_ = lean_ctor_get(v___y_4514_, 0);
v_options_4524_ = lean_ctor_get(v_toCold_4523_, 2);
v_inheritedTraceOptions_4525_ = lean_ctor_get(v_toCold_4523_, 11);
v_hasTrace_4526_ = lean_ctor_get_uint8(v_options_4524_, sizeof(void*)*1);
v___x_4527_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4526_ == 0)
{
v___y_4470_ = v___y_4513_;
v___y_4471_ = v___x_4527_;
v___y_4472_ = v___y_4515_;
v___y_4473_ = v___y_4516_;
v___y_4474_ = v___y_4511_;
v___y_4475_ = v___y_4517_;
v___y_4476_ = v___y_4514_;
v___y_4477_ = v___y_4518_;
goto v___jp_4469_;
}
else
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4525_, v_options_4524_, v___x_4528_);
if (v___x_4529_ == 0)
{
v___y_4470_ = v___y_4513_;
v___y_4471_ = v___x_4527_;
v___y_4472_ = v___y_4515_;
v___y_4473_ = v___y_4516_;
v___y_4474_ = v___y_4511_;
v___y_4475_ = v___y_4517_;
v___y_4476_ = v___y_4514_;
v___y_4477_ = v___y_4518_;
goto v___jp_4469_;
}
else
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4530_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4468_);
v___x_4531_ = l_Lean_MessageData_ofConstName(v___x_4468_, v___y_4512_);
v___x_4532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4530_);
lean_ctor_set(v___x_4532_, 1, v___x_4531_);
v___x_4533_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4527_, v___x_4532_, v___y_4511_, v___y_4517_, v___y_4514_, v___y_4518_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_dec_ref_known(v___x_4533_, 1);
v___y_4470_ = v___y_4513_;
v___y_4471_ = v___x_4527_;
v___y_4472_ = v___y_4515_;
v___y_4473_ = v___y_4516_;
v___y_4474_ = v___y_4511_;
v___y_4475_ = v___y_4517_;
v___y_4476_ = v___y_4514_;
v___y_4477_ = v___y_4518_;
goto v___jp_4469_;
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4511_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_dec(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4511_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4542_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4522_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4522_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4557_; 
lean_dec(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4511_);
lean_dec(v___x_4468_);
lean_dec(v_instName_4464_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4550_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4552_ = v___x_4521_;
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4521_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4555_; 
if (v_isShared_4553_ == 0)
{
v___x_4555_ = v___x_4552_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4550_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
v___jp_4558_:
{
lean_object* v___x_4567_; lean_object* v_env_4568_; uint8_t v_isNoncomputableSection_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4567_ = lean_st_ref_get(v___y_4566_);
v_env_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc_ref(v_env_4568_);
lean_dec(v___x_4567_);
v_isNoncomputableSection_4569_ = lean_ctor_get_uint8(v___y_4561_, sizeof(void*)*8 + 4);
v___x_4570_ = lean_unsigned_to_nat(1u);
v___x_4571_ = lean_mk_empty_array_with_capacity(v___x_4570_);
lean_inc(v___x_4468_);
v___x_4572_ = lean_array_push(v___x_4571_, v___x_4468_);
if (v_isNoncomputableSection_4569_ == 0)
{
lean_dec_ref(v_env_4568_);
v___y_4511_ = v___y_4563_;
v___y_4512_ = v___y_4560_;
v___y_4513_ = v___y_4559_;
v___y_4514_ = v___y_4565_;
v___y_4515_ = v___y_4561_;
v___y_4516_ = v___y_4562_;
v___y_4517_ = v___y_4564_;
v___y_4518_ = v___y_4566_;
v___y_4519_ = v___x_4572_;
v___y_4520_ = v___x_4442_;
goto v___jp_4510_;
}
else
{
uint8_t v___x_4573_; 
lean_inc(v___x_4468_);
v___x_4573_ = l_Lean_isMarkedMeta(v_env_4568_, v___x_4468_);
v___y_4511_ = v___y_4563_;
v___y_4512_ = v___y_4560_;
v___y_4513_ = v___y_4559_;
v___y_4514_ = v___y_4565_;
v___y_4515_ = v___y_4561_;
v___y_4516_ = v___y_4562_;
v___y_4517_ = v___y_4564_;
v___y_4518_ = v___y_4566_;
v___y_4519_ = v___x_4572_;
v___y_4520_ = v___x_4573_;
goto v___jp_4510_;
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v_ctorName_4445_);
lean_dec_ref(v___f_4444_);
lean_dec(v_inductiveTypeName_4441_);
v_a_4714_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4458_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4458_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
v___jp_4454_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4456_, 0, v___y_4455_);
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
return v___x_4457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4722_, lean_object* v___x_4723_, lean_object* v_inductiveTypeName_4724_, lean_object* v___x_4725_, lean_object* v___x_4726_, lean_object* v___f_4727_, lean_object* v_ctorName_4728_, lean_object* v_addHypotheses_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
uint8_t v___x_16682__boxed_4737_; uint8_t v_addHypotheses_boxed_4738_; lean_object* v_res_4739_; 
v___x_16682__boxed_4737_ = lean_unbox(v___x_4725_);
v_addHypotheses_boxed_4738_ = lean_unbox(v_addHypotheses_4729_);
v_res_4739_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4722_, v___x_4723_, v_inductiveTypeName_4724_, v___x_16682__boxed_4737_, v___x_4726_, v___f_4727_, v_ctorName_4728_, v_addHypotheses_boxed_4738_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
lean_dec(v___x_4726_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4742_, lean_object* v_ctorName_4743_, uint8_t v_addHypotheses_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v___f_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___f_4759_; uint8_t v___x_4760_; 
v___f_4752_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4753_ = lean_box(0);
v___x_4754_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4755_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4756_ = 1;
v___x_4757_ = lean_box(v___x_4756_);
v___x_4758_ = lean_box(v_addHypotheses_4744_);
lean_inc(v_ctorName_4743_);
v___f_4759_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4759_, 0, v___x_4754_);
lean_closure_set(v___f_4759_, 1, v___x_4755_);
lean_closure_set(v___f_4759_, 2, v_inductiveTypeName_4742_);
lean_closure_set(v___f_4759_, 3, v___x_4757_);
lean_closure_set(v___f_4759_, 4, v___x_4753_);
lean_closure_set(v___f_4759_, 5, v___f_4752_);
lean_closure_set(v___f_4759_, 6, v_ctorName_4743_);
lean_closure_set(v___f_4759_, 7, v___x_4758_);
v___x_4760_ = l_Lean_isPrivateName(v_ctorName_4743_);
lean_dec(v_ctorName_4743_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; 
v___x_4761_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4759_, v___x_4756_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
return v___x_4761_;
}
else
{
uint8_t v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = 0;
v___x_4763_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4759_, v___x_4762_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
return v___x_4763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4764_, lean_object* v_ctorName_4765_, lean_object* v_addHypotheses_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
uint8_t v_addHypotheses_boxed_4774_; lean_object* v_res_4775_; 
v_addHypotheses_boxed_4774_ = lean_unbox(v_addHypotheses_4766_);
v_res_4775_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4764_, v_ctorName_4765_, v_addHypotheses_boxed_4774_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4776_, lean_object* v_ctorName_4777_, uint8_t v_addHypotheses_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4782_ = lean_box(v_addHypotheses_4778_);
v___x_4783_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4783_, 0, v_inductiveTypeName_4776_);
lean_closure_set(v___x_4783_, 1, v_ctorName_4777_);
lean_closure_set(v___x_4783_, 2, v___x_4782_);
v___x_4784_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4783_, v_a_4779_, v_a_4780_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4814_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4814_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4814_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
if (lean_obj_tag(v_a_4785_) == 0)
{
uint8_t v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4789_ = 0;
v___x_4790_ = lean_box(v___x_4789_);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4790_);
v___x_4792_ = v___x_4787_;
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
else
{
lean_object* v_val_4794_; lean_object* v___x_4795_; 
lean_del_object(v___x_4787_);
v_val_4794_ = lean_ctor_get(v_a_4785_, 0);
lean_inc(v_val_4794_);
lean_dec_ref_known(v_a_4785_, 1);
v___x_4795_ = l_Lean_Elab_Command_elabCommand(v_val_4794_, v_a_4779_, v_a_4780_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4804_; 
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4804_ == 0)
{
lean_object* v_unused_4805_; 
v_unused_4805_ = lean_ctor_get(v___x_4795_, 0);
lean_dec(v_unused_4805_);
v___x_4797_ = v___x_4795_;
v_isShared_4798_ = v_isSharedCheck_4804_;
goto v_resetjp_4796_;
}
else
{
lean_dec(v___x_4795_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4804_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
uint8_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
v___x_4799_ = 1;
v___x_4800_ = lean_box(v___x_4799_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v___x_4800_);
v___x_4802_ = v___x_4797_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4800_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
v_a_4806_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4795_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4795_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
v_a_4815_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4784_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4784_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4823_, lean_object* v_ctorName_4824_, lean_object* v_addHypotheses_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
uint8_t v_addHypotheses_boxed_4829_; lean_object* v_res_4830_; 
v_addHypotheses_boxed_4829_ = lean_unbox(v_addHypotheses_4825_);
v_res_4830_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4823_, v_ctorName_4824_, v_addHypotheses_boxed_4829_, v_a_4826_, v_a_4827_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4834_, uint8_t v_addHypotheses_4835_, lean_object* v_as_x27_4836_, lean_object* v_b_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
if (lean_obj_tag(v_as_x27_4836_) == 0)
{
lean_object* v___x_4841_; 
lean_dec(v_declName_4834_);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v_b_4837_);
return v___x_4841_;
}
else
{
lean_object* v_head_4842_; lean_object* v_tail_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
lean_dec_ref(v_b_4837_);
v_head_4842_ = lean_ctor_get(v_as_x27_4836_, 0);
v_tail_4843_ = lean_ctor_get(v_as_x27_4836_, 1);
v___x_4844_ = lean_box(0);
v___x_4845_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
lean_inc(v_head_4842_);
lean_inc(v_declName_4834_);
v___x_4846_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4834_, v_head_4842_, v_addHypotheses_4835_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4858_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4858_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4858_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
uint8_t v___x_4851_; 
v___x_4851_ = lean_unbox(v_a_4847_);
if (v___x_4851_ == 0)
{
lean_del_object(v___x_4849_);
lean_dec(v_a_4847_);
v_as_x27_4836_ = v_tail_4843_;
v_b_4837_ = v___x_4845_;
goto _start;
}
else
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
lean_dec(v_declName_4834_);
v___x_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4853_, 0, v_a_4847_);
v___x_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
lean_ctor_set(v___x_4854_, 1, v___x_4844_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4854_);
v___x_4856_ = v___x_4849_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4854_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
else
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4866_; 
lean_dec(v_declName_4834_);
v_a_4859_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4861_ = v___x_4846_;
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4846_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4867_, lean_object* v_addHypotheses_4868_, lean_object* v_as_x27_4869_, lean_object* v_b_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
uint8_t v_addHypotheses_boxed_4874_; lean_object* v_res_4875_; 
v_addHypotheses_boxed_4874_ = lean_unbox(v_addHypotheses_4868_);
v_res_4875_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4867_, v_addHypotheses_boxed_4874_, v_as_x27_4869_, v_b_4870_, v___y_4871_, v___y_4872_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v_as_x27_4869_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4876_, lean_object* v_declName_4877_, uint8_t v_addHypotheses_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_){
_start:
{
lean_object* v_ctors_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v_ctors_4882_ = lean_ctor_get(v_a_4876_, 4);
v___x_4883_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4884_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4877_, v_addHypotheses_4878_, v_ctors_4882_, v___x_4883_, v___y_4879_, v___y_4880_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4899_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4887_ = v___x_4884_;
v_isShared_4888_ = v_isSharedCheck_4899_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4884_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4899_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v_fst_4889_; 
v_fst_4889_ = lean_ctor_get(v_a_4885_, 0);
lean_inc(v_fst_4889_);
lean_dec(v_a_4885_);
if (lean_obj_tag(v_fst_4889_) == 0)
{
uint8_t v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4893_; 
v___x_4890_ = 0;
v___x_4891_ = lean_box(v___x_4890_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v___x_4891_);
v___x_4893_ = v___x_4887_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
else
{
lean_object* v_val_4895_; lean_object* v___x_4897_; 
v_val_4895_ = lean_ctor_get(v_fst_4889_, 0);
lean_inc(v_val_4895_);
lean_dec_ref_known(v_fst_4889_, 1);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v_val_4895_);
v___x_4897_ = v___x_4887_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_val_4895_);
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
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
v_a_4900_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4884_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4884_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_4908_, lean_object* v_declName_4909_, lean_object* v_addHypotheses_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
uint8_t v_addHypotheses_boxed_4914_; lean_object* v_res_4915_; 
v_addHypotheses_boxed_4914_ = lean_unbox(v_addHypotheses_4910_);
v_res_4915_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_4908_, v_declName_4909_, v_addHypotheses_boxed_4914_, v___y_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec_ref(v_a_4908_);
return v_res_4915_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4916_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4916_);
return v___x_4917_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4918_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4919_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4920_ = lean_unsigned_to_nat(0u);
v___x_4921_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
lean_ctor_set(v___x_4921_, 1, v___x_4920_);
lean_ctor_set(v___x_4921_, 2, v___x_4920_);
lean_ctor_set(v___x_4921_, 3, v___x_4920_);
lean_ctor_set(v___x_4921_, 4, v___x_4919_);
lean_ctor_set(v___x_4921_, 5, v___x_4919_);
lean_ctor_set(v___x_4921_, 6, v___x_4919_);
lean_ctor_set(v___x_4921_, 7, v___x_4919_);
lean_ctor_set(v___x_4921_, 8, v___x_4919_);
lean_ctor_set(v___x_4921_, 9, v___x_4919_);
lean_ctor_set(v___x_4921_, 10, v___x_4918_);
return v___x_4921_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4922_ = lean_unsigned_to_nat(32u);
v___x_4923_ = lean_mk_empty_array_with_capacity(v___x_4922_);
v___x_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4923_);
return v___x_4924_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
size_t v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4925_ = ((size_t)5ULL);
v___x_4926_ = lean_unsigned_to_nat(0u);
v___x_4927_ = lean_unsigned_to_nat(32u);
v___x_4928_ = lean_mk_empty_array_with_capacity(v___x_4927_);
v___x_4929_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_4930_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4930_, 0, v___x_4929_);
lean_ctor_set(v___x_4930_, 1, v___x_4928_);
lean_ctor_set(v___x_4930_, 2, v___x_4926_);
lean_ctor_set(v___x_4930_, 3, v___x_4926_);
lean_ctor_set_usize(v___x_4930_, 4, v___x_4925_);
return v___x_4930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4931_ = lean_box(1);
v___x_4932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_4933_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4933_);
lean_ctor_set(v___x_4934_, 1, v___x_4932_);
lean_ctor_set(v___x_4934_, 2, v___x_4931_);
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v___x_4938_; lean_object* v_env_4939_; uint8_t v___x_4940_; lean_object* v_env_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v_scopes_4944_; lean_object* v___x_4945_; lean_object* v_opts_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4938_ = lean_st_ref_get(v___y_4936_);
v_env_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc_ref(v_env_4939_);
lean_dec(v___x_4938_);
v___x_4940_ = 0;
v_env_4941_ = l_Lean_Environment_setRecordingDeps(v_env_4939_, v___x_4940_);
v___x_4942_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4943_ = lean_st_ref_get(v___y_4936_);
v_scopes_4944_ = lean_ctor_get(v___x_4943_, 2);
lean_inc(v_scopes_4944_);
lean_dec(v___x_4943_);
v___x_4945_ = l_List_head_x21___redArg(v___x_4942_, v_scopes_4944_);
lean_dec(v_scopes_4944_);
v_opts_4946_ = lean_ctor_get(v___x_4945_, 1);
lean_inc_ref(v_opts_4946_);
lean_dec(v___x_4945_);
v___x_4947_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4948_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_4949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4949_, 0, v_env_4941_);
lean_ctor_set(v___x_4949_, 1, v___x_4947_);
lean_ctor_set(v___x_4949_, 2, v___x_4948_);
lean_ctor_set(v___x_4949_, 3, v_opts_4946_);
v___x_4950_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4949_);
lean_ctor_set(v___x_4950_, 1, v_msgData_4935_);
v___x_4951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_4952_, v___y_4953_);
lean_dec(v___y_4953_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_4956_, lean_object* v_macroStack_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v_scopes_4962_; lean_object* v___x_4963_; lean_object* v_opts_4964_; lean_object* v___x_4965_; uint8_t v___x_4966_; 
v___x_4960_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4961_ = lean_st_ref_get(v___y_4958_);
v_scopes_4962_ = lean_ctor_get(v___x_4961_, 2);
lean_inc(v_scopes_4962_);
lean_dec(v___x_4961_);
v___x_4963_ = l_List_head_x21___redArg(v___x_4960_, v_scopes_4962_);
lean_dec(v_scopes_4962_);
v_opts_4964_ = lean_ctor_get(v___x_4963_, 1);
lean_inc_ref(v_opts_4964_);
lean_dec(v___x_4963_);
v___x_4965_ = l_Lean_Elab_pp_macroStack;
v___x_4966_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_4964_, v___x_4965_);
lean_dec_ref(v_opts_4964_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; 
lean_dec(v_macroStack_4957_);
v___x_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4967_, 0, v_msgData_4956_);
return v___x_4967_;
}
else
{
if (lean_obj_tag(v_macroStack_4957_) == 0)
{
lean_object* v___x_4968_; 
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_msgData_4956_);
return v___x_4968_;
}
else
{
lean_object* v_head_4969_; lean_object* v_after_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4985_; 
v_head_4969_ = lean_ctor_get(v_macroStack_4957_, 0);
lean_inc(v_head_4969_);
v_after_4970_ = lean_ctor_get(v_head_4969_, 1);
v_isSharedCheck_4985_ = !lean_is_exclusive(v_head_4969_);
if (v_isSharedCheck_4985_ == 0)
{
lean_object* v_unused_4986_; 
v_unused_4986_ = lean_ctor_get(v_head_4969_, 0);
lean_dec(v_unused_4986_);
v___x_4972_ = v_head_4969_;
v_isShared_4973_ = v_isSharedCheck_4985_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_after_4970_);
lean_dec(v_head_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4985_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v___x_4976_; 
v___x_4974_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_4973_ == 0)
{
lean_ctor_set_tag(v___x_4972_, 7);
lean_ctor_set(v___x_4972_, 1, v___x_4974_);
lean_ctor_set(v___x_4972_, 0, v_msgData_4956_);
v___x_4976_ = v___x_4972_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_msgData_4956_);
lean_ctor_set(v_reuseFailAlloc_4984_, 1, v___x_4974_);
v___x_4976_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v_msgData_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4977_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_4978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set(v___x_4978_, 1, v___x_4977_);
v___x_4979_ = l_Lean_MessageData_ofSyntax(v_after_4970_);
v___x_4980_ = l_Lean_indentD(v___x_4979_);
v_msgData_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4981_, 0, v___x_4978_);
lean_ctor_set(v_msgData_4981_, 1, v___x_4980_);
v___x_4982_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_4981_, v_macroStack_4957_);
v___x_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
return v___x_4983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_4987_, lean_object* v_macroStack_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_4987_, v_macroStack_4988_, v___y_4989_);
lean_dec(v___y_4989_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = l_Lean_Elab_Command_getRef___redArg(v___y_4993_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_a_4997_; lean_object* v_macroStack_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v_a_5001_; lean_object* v___x_5002_; lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5011_; 
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc(v_a_4997_);
lean_dec_ref_known(v___x_4996_, 1);
v_macroStack_4998_ = lean_ctor_get(v___y_4993_, 4);
v___x_4999_ = l_Lean_Elab_getBetterRef(v_a_4997_, v_macroStack_4998_);
lean_dec(v_a_4997_);
v___x_5000_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_4992_, v___y_4994_);
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
lean_inc(v_a_5001_);
lean_dec_ref(v___x_5000_);
lean_inc(v_macroStack_4998_);
v___x_5002_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_5001_, v_macroStack_4998_, v___y_4994_);
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5005_ = v___x_5002_;
v_isShared_5006_ = v_isSharedCheck_5011_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_5002_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5011_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5007_; lean_object* v___x_5009_; 
v___x_5007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_4999_);
lean_ctor_set(v___x_5007_, 1, v_a_5003_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set_tag(v___x_5005_, 1);
lean_ctor_set(v___x_5005_, 0, v___x_5007_);
v___x_5009_ = v___x_5005_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_dec_ref(v_msg_4992_);
v_a_5012_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_4996_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_4996_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5020_, v___y_5021_, v___y_5022_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v___x_5029_; lean_object* v_env_5030_; lean_object* v___x_5031_; 
v___x_5029_ = lean_st_ref_get(v___y_5027_);
v_env_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc_ref(v_env_5030_);
lean_dec(v___x_5029_);
lean_inc(v_constName_5025_);
v___x_5031_ = l_Lean_isInductiveCore_x3f(v_env_5030_, v_constName_5025_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v___x_5032_; uint8_t v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5032_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5033_ = 0;
v___x_5034_ = l_Lean_MessageData_ofConstName(v_constName_5025_, v___x_5033_);
v___x_5035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5032_);
lean_ctor_set(v___x_5035_, 1, v___x_5034_);
v___x_5036_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5035_);
lean_ctor_set(v___x_5037_, 1, v___x_5036_);
v___x_5038_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5037_, v___y_5026_, v___y_5027_);
return v___x_5038_;
}
else
{
lean_object* v_val_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
lean_dec(v_constName_5025_);
v_val_5039_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5031_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_val_5039_);
lean_dec(v___x_5031_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
lean_ctor_set_tag(v___x_5041_, 0);
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_val_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5047_, v___y_5048_, v___y_5049_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
return v_res_5051_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5054_ = l_Lean_stringToMessageData(v___x_5053_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_){
_start:
{
lean_object* v___x_5062_; 
lean_inc(v_declName_5055_);
v___x_5062_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5055_, v___y_5056_, v___y_5057_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; uint8_t v___x_5064_; lean_object* v___x_5065_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5062_, 1);
v___x_5064_ = 0;
lean_inc(v_declName_5055_);
v___x_5065_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5063_, v_declName_5055_, v___x_5064_, v___y_5056_, v___y_5057_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; uint8_t v___x_5067_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___x_5065_, 1);
v___x_5067_ = lean_unbox(v_a_5066_);
lean_dec(v_a_5066_);
if (v___x_5067_ == 0)
{
uint8_t v___x_5068_; lean_object* v___x_5069_; 
v___x_5068_ = 1;
lean_inc(v_declName_5055_);
v___x_5069_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5063_, v_declName_5055_, v___x_5068_, v___y_5056_, v___y_5057_);
lean_dec(v_a_5063_);
if (lean_obj_tag(v___x_5069_) == 0)
{
lean_object* v_a_5070_; uint8_t v___x_5071_; 
v_a_5070_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_a_5070_);
lean_dec_ref_known(v___x_5069_, 1);
v___x_5071_ = lean_unbox(v_a_5070_);
lean_dec(v_a_5070_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5072_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5073_ = l_Lean_MessageData_ofConstName(v_declName_5055_, v___x_5064_);
v___x_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5072_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
v___x_5075_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5076_, v___y_5056_, v___y_5057_);
return v___x_5077_;
}
else
{
lean_dec(v_declName_5055_);
goto v___jp_5059_;
}
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
lean_dec(v_declName_5055_);
v_a_5078_ = lean_ctor_get(v___x_5069_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v___x_5069_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5069_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
else
{
lean_dec(v_a_5063_);
lean_dec(v_declName_5055_);
goto v___jp_5059_;
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_dec(v_a_5063_);
lean_dec(v_declName_5055_);
v_a_5086_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5065_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5065_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec(v_declName_5055_);
v_a_5094_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5062_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5062_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
v___jp_5059_:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5060_ = lean_box(0);
v___x_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5060_);
return v___x_5061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5102_, v___y_5103_, v___y_5104_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v___f_5111_; lean_object* v___x_5112_; 
lean_inc(v_declName_5107_);
v___f_5111_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5111_, 0, v_declName_5107_);
v___x_5112_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5107_, v___f_5111_, v_a_5108_, v_a_5109_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5113_, v_a_5114_, v_a_5115_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5118_, uint8_t v_addHypotheses_5119_, lean_object* v_as_5120_, lean_object* v_as_x27_5121_, lean_object* v_b_5122_, lean_object* v_a_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5118_, v_addHypotheses_5119_, v_as_x27_5121_, v_b_5122_, v___y_5124_, v___y_5125_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5128_, lean_object* v_addHypotheses_5129_, lean_object* v_as_5130_, lean_object* v_as_x27_5131_, lean_object* v_b_5132_, lean_object* v_a_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
uint8_t v_addHypotheses_boxed_5137_; lean_object* v_res_5138_; 
v_addHypotheses_boxed_5137_ = lean_unbox(v_addHypotheses_5129_);
v_res_5138_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5128_, v_addHypotheses_boxed_5137_, v_as_5130_, v_as_x27_5131_, v_b_5132_, v_a_5133_, v___y_5134_, v___y_5135_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec(v_as_x27_5131_);
lean_dec(v_as_5130_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5139_, v___y_5141_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v_res_5148_; 
v_res_5148_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5144_, v___y_5145_, v___y_5146_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5149_, lean_object* v_msg_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5150_, v___y_5151_, v___y_5152_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5155_, lean_object* v_msg_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5155_, v_msg_5156_, v___y_5157_, v___y_5158_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5161_, lean_object* v_macroStack_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5161_, v_macroStack_5162_, v___y_5164_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5167_, lean_object* v_macroStack_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5167_, v_macroStack_5168_, v___y_5169_, v___y_5170_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v___x_5176_; lean_object* v_env_5177_; uint8_t v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5176_ = lean_st_ref_get(v___y_5174_);
v_env_5177_ = lean_ctor_get(v___x_5176_, 0);
lean_inc_ref(v_env_5177_);
lean_dec(v___x_5176_);
v___x_5178_ = l_Lean_isInductiveCore(v_env_5177_, v_declName_5173_);
v___x_5179_ = lean_box(v___x_5178_);
v___x_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5181_, v___y_5182_);
lean_dec(v___y_5182_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5185_, v___y_5187_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5190_, v___y_5191_, v___y_5192_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
if (v_____do__lift_5195_ == 0)
{
uint8_t v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5199_ = 1;
v___x_5200_ = lean_box(v___x_5199_);
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
return v___x_5201_;
}
else
{
uint8_t v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; 
v___x_5202_ = 0;
v___x_5203_ = lean_box(v___x_5202_);
v___x_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5203_);
return v___x_5204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
uint8_t v_____do__lift_1604__boxed_5209_; lean_object* v_res_5210_; 
v_____do__lift_1604__boxed_5209_ = lean_unbox(v_____do__lift_5205_);
v_res_5210_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1604__boxed_5209_, v___y_5206_, v___y_5207_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5211_, size_t v_i_5212_, size_t v_stop_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
uint8_t v___x_5217_; 
v___x_5217_ = lean_usize_dec_eq(v_i_5212_, v_stop_5213_);
if (v___x_5217_ == 0)
{
uint8_t v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v___x_5218_ = 1;
v___x_5219_ = lean_array_uget_borrowed(v_as_5211_, v_i_5212_);
lean_inc(v___x_5219_);
v___x_5220_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5219_, v___y_5215_);
if (lean_obj_tag(v___x_5220_) == 0)
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5233_; 
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5220_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5223_ = v___x_5220_;
v_isShared_5224_ = v_isSharedCheck_5233_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5220_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5233_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
uint8_t v___x_5225_; 
v___x_5225_ = lean_unbox(v_a_5221_);
lean_dec(v_a_5221_);
if (v___x_5225_ == 0)
{
lean_object* v___x_5226_; lean_object* v___x_5228_; 
v___x_5226_ = lean_box(v___x_5218_);
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 0, v___x_5226_);
v___x_5228_ = v___x_5223_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5226_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
else
{
size_t v___x_5230_; size_t v___x_5231_; 
lean_del_object(v___x_5223_);
v___x_5230_ = ((size_t)1ULL);
v___x_5231_ = lean_usize_add(v_i_5212_, v___x_5230_);
v_i_5212_ = v___x_5231_;
goto _start;
}
}
}
else
{
return v___x_5220_;
}
}
else
{
uint8_t v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5234_ = 0;
v___x_5235_ = lean_box(v___x_5234_);
v___x_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5235_);
return v___x_5236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5237_, lean_object* v_i_5238_, lean_object* v_stop_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
size_t v_i_boxed_5243_; size_t v_stop_boxed_5244_; lean_object* v_res_5245_; 
v_i_boxed_5243_ = lean_unbox_usize(v_i_5238_);
lean_dec(v_i_5238_);
v_stop_boxed_5244_ = lean_unbox_usize(v_stop_5239_);
lean_dec(v_stop_5239_);
v_res_5245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5237_, v_i_boxed_5243_, v_stop_boxed_5244_, v___y_5240_, v___y_5241_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec_ref(v_as_5237_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5246_, size_t v_i_5247_, size_t v_stop_5248_, lean_object* v_b_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
uint8_t v___x_5253_; 
v___x_5253_ = lean_usize_dec_eq(v_i_5247_, v_stop_5248_);
if (v___x_5253_ == 0)
{
lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5254_ = lean_array_uget_borrowed(v_as_5246_, v_i_5247_);
lean_inc(v___x_5254_);
v___x_5255_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5254_, v___y_5250_, v___y_5251_);
if (lean_obj_tag(v___x_5255_) == 0)
{
lean_object* v_a_5256_; size_t v___x_5257_; size_t v___x_5258_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
lean_inc(v_a_5256_);
lean_dec_ref_known(v___x_5255_, 1);
v___x_5257_ = ((size_t)1ULL);
v___x_5258_ = lean_usize_add(v_i_5247_, v___x_5257_);
v_i_5247_ = v___x_5258_;
v_b_5249_ = v_a_5256_;
goto _start;
}
else
{
return v___x_5255_;
}
}
else
{
lean_object* v___x_5260_; 
v___x_5260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5260_, 0, v_b_5249_);
return v___x_5260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5261_, lean_object* v_i_5262_, lean_object* v_stop_5263_, lean_object* v_b_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
size_t v_i_boxed_5268_; size_t v_stop_boxed_5269_; lean_object* v_res_5270_; 
v_i_boxed_5268_ = lean_unbox_usize(v_i_5262_);
lean_dec(v_i_5262_);
v_stop_boxed_5269_ = lean_unbox_usize(v_stop_5263_);
lean_dec(v_stop_5263_);
v_res_5270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5261_, v_i_boxed_5268_, v_stop_boxed_5269_, v_b_5264_, v___y_5265_, v___y_5266_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec_ref(v_as_5261_);
return v_res_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_){
_start:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___y_5304_; uint8_t v___x_5307_; 
v___x_5275_ = lean_unsigned_to_nat(0u);
v___x_5276_ = lean_array_get_size(v_declNames_5271_);
v___x_5307_ = lean_nat_dec_lt(v___x_5275_, v___x_5276_);
if (v___x_5307_ == 0)
{
lean_object* v___x_5308_; 
v___x_5308_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5307_, v_a_5272_, v_a_5273_);
v___y_5304_ = v___x_5308_;
goto v___jp_5303_;
}
else
{
if (v___x_5307_ == 0)
{
goto v___jp_5277_;
}
else
{
size_t v___x_5309_; size_t v___x_5310_; lean_object* v___x_5311_; 
v___x_5309_ = ((size_t)0ULL);
v___x_5310_ = lean_usize_of_nat(v___x_5276_);
v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5271_, v___x_5309_, v___x_5310_, v_a_5272_, v_a_5273_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; uint8_t v___x_5313_; lean_object* v___x_5314_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_a_5312_);
lean_dec_ref_known(v___x_5311_, 1);
v___x_5313_ = lean_unbox(v_a_5312_);
lean_dec(v_a_5312_);
v___x_5314_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5313_, v_a_5272_, v_a_5273_);
v___y_5304_ = v___x_5314_;
goto v___jp_5303_;
}
else
{
return v___x_5311_;
}
}
}
v___jp_5277_:
{
uint8_t v___x_5278_; uint8_t v___x_5279_; 
v___x_5278_ = 1;
v___x_5279_ = lean_nat_dec_lt(v___x_5275_, v___x_5276_);
if (v___x_5279_ == 0)
{
lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5280_ = lean_box(v___x_5278_);
v___x_5281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5281_, 0, v___x_5280_);
return v___x_5281_;
}
else
{
lean_object* v___x_5282_; size_t v___x_5283_; size_t v___x_5284_; lean_object* v___x_5285_; 
v___x_5282_ = lean_box(0);
v___x_5283_ = ((size_t)0ULL);
v___x_5284_ = lean_usize_of_nat(v___x_5276_);
v___x_5285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5271_, v___x_5283_, v___x_5284_, v___x_5282_, v_a_5272_, v_a_5273_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5293_; 
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5293_ == 0)
{
lean_object* v_unused_5294_; 
v_unused_5294_ = lean_ctor_get(v___x_5285_, 0);
lean_dec(v_unused_5294_);
v___x_5287_ = v___x_5285_;
v_isShared_5288_ = v_isSharedCheck_5293_;
goto v_resetjp_5286_;
}
else
{
lean_dec(v___x_5285_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5293_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5289_ = lean_box(v___x_5278_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5289_);
v___x_5291_ = v___x_5287_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
else
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
v_a_5295_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___x_5285_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5285_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5300_; 
if (v_isShared_5298_ == 0)
{
v___x_5300_ = v___x_5297_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
}
v___jp_5303_:
{
lean_object* v_a_5305_; uint8_t v___x_5306_; 
v_a_5305_ = lean_ctor_get(v___y_5304_, 0);
v___x_5306_ = lean_unbox(v_a_5305_);
if (v___x_5306_ == 0)
{
return v___y_5304_;
}
else
{
lean_dec_ref(v___y_5304_);
goto v___jp_5277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5315_, v_a_5316_, v_a_5317_);
lean_dec(v_a_5317_);
lean_dec_ref(v_a_5316_);
lean_dec_ref(v_declNames_5315_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5384_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5385_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5386_ = l_Lean_Elab_registerDerivingHandler(v___x_5384_, v___x_5385_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v___x_5387_; uint8_t v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
lean_dec_ref_known(v___x_5386_, 1);
v___x_5387_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5388_ = 0;
v___x_5389_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5390_ = l_Lean_registerTraceClass(v___x_5387_, v___x_5388_, v___x_5389_);
return v___x_5390_;
}
else
{
return v___x_5386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5391_){
_start:
{
lean_object* v_res_5392_; 
v_res_5392_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5392_;
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
