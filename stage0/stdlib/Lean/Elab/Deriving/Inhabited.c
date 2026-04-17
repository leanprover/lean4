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
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_runST___redArg(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_inlineExprTrailing(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
static lean_once_cell_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___closed__0;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object*);
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
v___x_159_ = lean_st_ref_set(v___y_120_, v___x_158_);
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
lean_dec_ref(v_a_216_);
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
v___x_244_ = lean_array_push(v___x_243_, v_head_228_);
v___x_245_ = l_Lean_Meta_mkAppM(v___x_241_, v___x_244_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_n(v_a_246_, 2);
lean_dec_ref(v___x_245_);
v___x_247_ = l_Lean_Meta_check(v_a_246_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref(v___x_247_);
v___x_248_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__3));
v___x_249_ = l_Lean_Core_mkFreshUserName(v___x_248_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___f_251_; uint8_t v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref(v___x_249_);
lean_inc(v_a_246_);
lean_inc(v_tail_229_);
lean_inc_ref(v_k_215_);
lean_inc(v_a_219_);
lean_inc_ref(v_a_218_);
lean_inc(v_a_217_);
v___f_251_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___boxed), 15, 7);
lean_closure_set(v___f_251_, 0, v_a_217_);
lean_closure_set(v___f_251_, 1, v___x_242_);
lean_closure_set(v___f_251_, 2, v_a_218_);
lean_closure_set(v___f_251_, 3, v_a_219_);
lean_closure_set(v___f_251_, 4, v_k_215_);
lean_closure_set(v___f_251_, 5, v_tail_229_);
lean_closure_set(v___f_251_, 6, v_a_246_);
v___x_252_ = 3;
v___x_253_ = 0;
v___x_254_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__1___redArg(v_a_250_, v___x_252_, v_a_246_, v___f_251_, v___x_253_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_dec(v_tail_229_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_k_215_);
return v___x_254_;
}
else
{
lean_object* v_a_255_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
v___y_237_ = v___x_254_;
v_a_238_ = v_a_255_;
goto v___jp_236_;
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_246_);
v_a_256_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_249_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_249_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
lean_inc(v_a_256_);
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
v___y_237_ = v___x_261_;
v_a_238_ = v_a_256_;
goto v___jp_236_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_246_);
v_a_264_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_247_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_247_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
lean_inc(v_a_264_);
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
v___y_237_ = v___x_269_;
v_a_238_ = v_a_264_;
goto v___jp_236_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_245_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_245_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
lean_inc(v_a_272_);
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
v___y_237_ = v___x_277_;
v_a_238_ = v_a_272_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0(lean_object* v_a_280_, lean_object* v___x_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_k_284_, lean_object* v_tail_285_, lean_object* v_a_286_, lean_object* v_inst_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v_options_307_; uint8_t v_hasTrace_308_; 
v_options_307_ = lean_ctor_get(v___y_292_, 2);
v_hasTrace_308_ = lean_ctor_get_uint8(v_options_307_, sizeof(void*)*1);
if (v_hasTrace_308_ == 0)
{
lean_dec_ref(v_a_286_);
v___y_296_ = v___y_288_;
v___y_297_ = v___y_289_;
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
goto v___jp_295_;
}
else
{
lean_object* v_inheritedTraceOptions_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_inheritedTraceOptions_309_ = lean_ctor_get(v___y_292_, 13);
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_311_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_312_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_309_, v_options_307_, v___x_311_);
if (v___x_312_ == 0)
{
lean_dec_ref(v_a_286_);
v___y_296_ = v___y_288_;
v___y_297_ = v___y_289_;
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
goto v___jp_295_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__8);
v___x_314_ = l_Lean_MessageData_ofExpr(v_a_286_);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_310_, v___x_315_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_dec_ref(v___x_316_);
v___y_296_ = v___y_288_;
v___y_297_ = v___y_289_;
v___y_298_ = v___y_290_;
v___y_299_ = v___y_291_;
v___y_300_ = v___y_292_;
v___y_301_ = v___y_293_;
goto v___jp_295_;
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_inst_287_);
lean_dec(v_tail_285_);
lean_dec_ref(v_k_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_280_);
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
v___jp_295_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_302_ = lean_nat_add(v_a_280_, v___x_281_);
lean_inc_ref(v_inst_287_);
v___x_303_ = lean_array_push(v_a_282_, v_inst_287_);
v___x_304_ = l_Lean_Expr_fvarId_x21(v_inst_287_);
lean_dec_ref(v_inst_287_);
v___x_305_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_304_, v_a_280_, v_a_283_);
v___x_306_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_284_, v_tail_285_, v___x_302_, v___x_303_, v___x_305_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___boxed(lean_object* v_k_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(lean_object* v_00_u03b1_338_, lean_object* v_k_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___boxed(lean_object* v_00_u03b1_352_, lean_object* v_k_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux(v_00_u03b1_352_, v_k_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(lean_object* v_cls_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v_cls_366_, v_msg_367_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___boxed(lean_object* v_cls_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0(v_cls_376_, v_msg_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(uint8_t v_addHypotheses_388_, lean_object* v_xs_389_, lean_object* v_k_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
if (v_addHypotheses_388_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v_xs_389_);
v___x_398_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_399_ = lean_box(1);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
lean_inc(v_a_392_);
lean_inc_ref(v_a_391_);
v___x_400_ = lean_apply_9(v_k_390_, v___x_398_, v___x_399_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, lean_box(0));
return v___x_400_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_401_ = lean_array_to_list(v_xs_389_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___closed__0));
v___x_404_ = lean_box(1);
v___x_405_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg(v_k_390_, v___x_401_, v___x_402_, v___x_403_, v___x_404_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg___boxed(lean_object* v_addHypotheses_406_, lean_object* v_xs_407_, lean_object* v_k_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
uint8_t v_addHypotheses_boxed_416_; lean_object* v_res_417_; 
v_addHypotheses_boxed_416_ = lean_unbox(v_addHypotheses_406_);
v_res_417_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_boxed_416_, v_xs_407_, v_k_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(uint8_t v_addHypotheses_418_, lean_object* v_00_u03b1_419_, lean_object* v_xs_420_, lean_object* v_k_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___redArg(v_addHypotheses_418_, v_xs_420_, v_k_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed(lean_object* v_addHypotheses_430_, lean_object* v_00_u03b1_431_, lean_object* v_xs_432_, lean_object* v_k_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
uint8_t v_addHypotheses_boxed_441_; lean_object* v_res_442_; 
v_addHypotheses_boxed_441_ = lean_unbox(v_addHypotheses_430_);
v_res_442_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams(v_addHypotheses_boxed_441_, v_00_u03b1_431_, v_xs_432_, v_k_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(lean_object* v_k_443_, lean_object* v_v_444_, lean_object* v_t_445_){
_start:
{
if (lean_obj_tag(v_t_445_) == 0)
{
lean_object* v_size_446_; lean_object* v_k_447_; lean_object* v_v_448_; lean_object* v_l_449_; lean_object* v_r_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_731_; 
v_size_446_ = lean_ctor_get(v_t_445_, 0);
v_k_447_ = lean_ctor_get(v_t_445_, 1);
v_v_448_ = lean_ctor_get(v_t_445_, 2);
v_l_449_ = lean_ctor_get(v_t_445_, 3);
v_r_450_ = lean_ctor_get(v_t_445_, 4);
v_isSharedCheck_731_ = !lean_is_exclusive(v_t_445_);
if (v_isSharedCheck_731_ == 0)
{
v___x_452_ = v_t_445_;
v_isShared_453_ = v_isSharedCheck_731_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_r_450_);
lean_inc(v_l_449_);
lean_inc(v_v_448_);
lean_inc(v_k_447_);
lean_inc(v_size_446_);
lean_dec(v_t_445_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_731_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_lt(v_k_443_, v_k_447_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = lean_nat_dec_eq(v_k_443_, v_k_447_);
if (v___x_455_ == 0)
{
lean_object* v_impl_456_; lean_object* v___x_457_; 
lean_dec(v_size_446_);
v_impl_456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_443_, v_v_444_, v_r_450_);
v___x_457_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_449_) == 0)
{
lean_object* v_size_458_; lean_object* v_size_459_; lean_object* v_k_460_; lean_object* v_v_461_; lean_object* v_l_462_; lean_object* v_r_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_size_458_ = lean_ctor_get(v_l_449_, 0);
v_size_459_ = lean_ctor_get(v_impl_456_, 0);
lean_inc(v_size_459_);
v_k_460_ = lean_ctor_get(v_impl_456_, 1);
lean_inc(v_k_460_);
v_v_461_ = lean_ctor_get(v_impl_456_, 2);
lean_inc(v_v_461_);
v_l_462_ = lean_ctor_get(v_impl_456_, 3);
lean_inc(v_l_462_);
v_r_463_ = lean_ctor_get(v_impl_456_, 4);
lean_inc(v_r_463_);
v___x_464_ = lean_unsigned_to_nat(3u);
v___x_465_ = lean_nat_mul(v___x_464_, v_size_458_);
v___x_466_ = lean_nat_dec_lt(v___x_465_, v_size_459_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec(v_r_463_);
lean_dec(v_l_462_);
lean_dec(v_v_461_);
lean_dec(v_k_460_);
v___x_467_ = lean_nat_add(v___x_457_, v_size_458_);
v___x_468_ = lean_nat_add(v___x_467_, v_size_459_);
lean_dec(v_size_459_);
lean_dec(v___x_467_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_impl_456_);
lean_ctor_set(v___x_452_, 0, v___x_468_);
v___x_470_ = v___x_452_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_l_449_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_impl_456_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_535_; 
v_isSharedCheck_535_ = !lean_is_exclusive(v_impl_456_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; 
v_unused_536_ = lean_ctor_get(v_impl_456_, 4);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_impl_456_, 3);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_impl_456_, 2);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_impl_456_, 1);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_impl_456_, 0);
lean_dec(v_unused_540_);
v___x_473_ = v_impl_456_;
v_isShared_474_ = v_isSharedCheck_535_;
goto v_resetjp_472_;
}
else
{
lean_dec(v_impl_456_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_535_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_size_475_; lean_object* v_k_476_; lean_object* v_v_477_; lean_object* v_l_478_; lean_object* v_r_479_; lean_object* v_size_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_size_475_ = lean_ctor_get(v_l_462_, 0);
v_k_476_ = lean_ctor_get(v_l_462_, 1);
v_v_477_ = lean_ctor_get(v_l_462_, 2);
v_l_478_ = lean_ctor_get(v_l_462_, 3);
v_r_479_ = lean_ctor_get(v_l_462_, 4);
v_size_480_ = lean_ctor_get(v_r_463_, 0);
v___x_481_ = lean_unsigned_to_nat(2u);
v___x_482_ = lean_nat_mul(v___x_481_, v_size_480_);
v___x_483_ = lean_nat_dec_lt(v_size_475_, v___x_482_);
lean_dec(v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_511_; 
lean_inc(v_r_479_);
lean_inc(v_l_478_);
lean_inc(v_v_477_);
lean_inc(v_k_476_);
v_isSharedCheck_511_ = !lean_is_exclusive(v_l_462_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; 
v_unused_512_ = lean_ctor_get(v_l_462_, 4);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_l_462_, 3);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_l_462_, 2);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_l_462_, 1);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_l_462_, 0);
lean_dec(v_unused_516_);
v___x_485_ = v_l_462_;
v_isShared_486_ = v_isSharedCheck_511_;
goto v_resetjp_484_;
}
else
{
lean_dec(v_l_462_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_511_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_501_; 
v___x_487_ = lean_nat_add(v___x_457_, v_size_458_);
v___x_488_ = lean_nat_add(v___x_487_, v_size_459_);
lean_dec(v_size_459_);
if (lean_obj_tag(v_l_478_) == 0)
{
lean_object* v_size_509_; 
v_size_509_ = lean_ctor_get(v_l_478_, 0);
lean_inc(v_size_509_);
v___y_501_ = v_size_509_;
goto v___jp_500_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___y_501_ = v___x_510_;
goto v___jp_500_;
}
v___jp_489_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_nat_add(v___y_490_, v___y_492_);
lean_dec(v___y_492_);
lean_dec(v___y_490_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 4, v_r_463_);
lean_ctor_set(v___x_485_, 3, v_r_479_);
lean_ctor_set(v___x_485_, 2, v_v_461_);
lean_ctor_set(v___x_485_, 1, v_k_460_);
lean_ctor_set(v___x_485_, 0, v___x_493_);
v___x_495_ = v___x_485_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_v_461_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_r_479_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_r_463_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v___x_495_);
lean_ctor_set(v___x_473_, 3, v___y_491_);
lean_ctor_set(v___x_473_, 2, v_v_477_);
lean_ctor_set(v___x_473_, 1, v_k_476_);
lean_ctor_set(v___x_473_, 0, v___x_488_);
v___x_497_ = v___x_473_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_k_476_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_v_477_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v___y_491_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_nat_add(v___x_487_, v___y_501_);
lean_dec(v___y_501_);
lean_dec(v___x_487_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_l_478_);
lean_ctor_set(v___x_452_, 0, v___x_502_);
v___x_504_ = v___x_452_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_l_449_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_l_478_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_nat_add(v___x_457_, v_size_480_);
if (lean_obj_tag(v_r_479_) == 0)
{
lean_object* v_size_506_; 
v_size_506_ = lean_ctor_get(v_r_479_, 0);
lean_inc(v_size_506_);
v___y_490_ = v___x_505_;
v___y_491_ = v___x_504_;
v___y_492_ = v_size_506_;
goto v___jp_489_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___y_490_ = v___x_505_;
v___y_491_ = v___x_504_;
v___y_492_ = v___x_507_;
goto v___jp_489_;
}
}
}
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
lean_del_object(v___x_452_);
v___x_517_ = lean_nat_add(v___x_457_, v_size_458_);
v___x_518_ = lean_nat_add(v___x_517_, v_size_459_);
lean_dec(v_size_459_);
v___x_519_ = lean_nat_add(v___x_517_, v_size_475_);
lean_dec(v___x_517_);
lean_inc_ref(v_l_449_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_l_462_);
lean_ctor_set(v___x_473_, 3, v_l_449_);
lean_ctor_set(v___x_473_, 2, v_v_448_);
lean_ctor_set(v___x_473_, 1, v_k_447_);
lean_ctor_set(v___x_473_, 0, v___x_519_);
v___x_521_ = v___x_473_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_l_449_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v_l_462_);
v___x_521_ = v_reuseFailAlloc_534_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_isSharedCheck_528_ = !lean_is_exclusive(v_l_449_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_529_ = lean_ctor_get(v_l_449_, 4);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_l_449_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_l_449_, 2);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_l_449_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_l_449_, 0);
lean_dec(v_unused_533_);
v___x_523_ = v_l_449_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_l_449_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 4, v_r_463_);
lean_ctor_set(v___x_523_, 3, v___x_521_);
lean_ctor_set(v___x_523_, 2, v_v_461_);
lean_ctor_set(v___x_523_, 1, v_k_460_);
lean_ctor_set(v___x_523_, 0, v___x_518_);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_v_461_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v_r_463_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_541_; 
v_l_541_ = lean_ctor_get(v_impl_456_, 3);
lean_inc(v_l_541_);
if (lean_obj_tag(v_l_541_) == 0)
{
lean_object* v_r_542_; lean_object* v_k_543_; lean_object* v_v_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_567_; 
v_r_542_ = lean_ctor_get(v_impl_456_, 4);
v_k_543_ = lean_ctor_get(v_impl_456_, 1);
v_v_544_ = lean_ctor_get(v_impl_456_, 2);
v_isSharedCheck_567_ = !lean_is_exclusive(v_impl_456_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_568_ = lean_ctor_get(v_impl_456_, 3);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_impl_456_, 0);
lean_dec(v_unused_569_);
v___x_546_ = v_impl_456_;
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_r_542_);
lean_inc(v_v_544_);
lean_inc(v_k_543_);
lean_dec(v_impl_456_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_k_548_; lean_object* v_v_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_563_; 
v_k_548_ = lean_ctor_get(v_l_541_, 1);
v_v_549_ = lean_ctor_get(v_l_541_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v_l_541_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; 
v_unused_564_ = lean_ctor_get(v_l_541_, 4);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_l_541_, 3);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_541_, 0);
lean_dec(v_unused_566_);
v___x_551_ = v_l_541_;
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_v_549_);
lean_inc(v_k_548_);
lean_dec(v_l_541_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_542_, 2);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 4, v_r_542_);
lean_ctor_set(v___x_551_, 3, v_r_542_);
lean_ctor_set(v___x_551_, 2, v_v_448_);
lean_ctor_set(v___x_551_, 1, v_k_447_);
lean_ctor_set(v___x_551_, 0, v___x_457_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_r_542_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_r_542_);
v___x_555_ = v_reuseFailAlloc_562_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
lean_inc(v_r_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 3, v_r_542_);
lean_ctor_set(v___x_546_, 0, v___x_457_);
v___x_557_ = v___x_546_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_543_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_544_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_r_542_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_r_542_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v___x_557_);
lean_ctor_set(v___x_452_, 3, v___x_555_);
lean_ctor_set(v___x_452_, 2, v_v_549_);
lean_ctor_set(v___x_452_, 1, v_k_548_);
lean_ctor_set(v___x_452_, 0, v___x_553_);
v___x_559_ = v___x_452_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_549_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
else
{
lean_object* v_r_570_; 
v_r_570_ = lean_ctor_get(v_impl_456_, 4);
lean_inc(v_r_570_);
if (lean_obj_tag(v_r_570_) == 0)
{
lean_object* v_k_571_; lean_object* v_v_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_583_; 
v_k_571_ = lean_ctor_get(v_impl_456_, 1);
v_v_572_ = lean_ctor_get(v_impl_456_, 2);
v_isSharedCheck_583_ = !lean_is_exclusive(v_impl_456_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_584_ = lean_ctor_get(v_impl_456_, 4);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_impl_456_, 3);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_impl_456_, 0);
lean_dec(v_unused_586_);
v___x_574_ = v_impl_456_;
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_v_572_);
lean_inc(v_k_571_);
lean_dec(v_impl_456_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_unsigned_to_nat(3u);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 4, v_l_541_);
lean_ctor_set(v___x_574_, 2, v_v_448_);
lean_ctor_set(v___x_574_, 1, v_k_447_);
lean_ctor_set(v___x_574_, 0, v___x_457_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_l_541_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v_l_541_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_580_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_r_570_);
lean_ctor_set(v___x_452_, 3, v___x_578_);
lean_ctor_set(v___x_452_, 2, v_v_572_);
lean_ctor_set(v___x_452_, 1, v_k_571_);
lean_ctor_set(v___x_452_, 0, v___x_576_);
v___x_580_ = v___x_452_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_k_571_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_v_572_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_r_570_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(2u);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_impl_456_);
lean_ctor_set(v___x_452_, 3, v_r_570_);
lean_ctor_set(v___x_452_, 0, v___x_587_);
v___x_589_ = v___x_452_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_r_570_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_impl_456_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec(v_v_448_);
lean_dec(v_k_447_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 2, v_v_444_);
lean_ctor_set(v___x_452_, 1, v_k_443_);
v___x_592_ = v___x_452_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_size_446_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_443_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_444_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_l_449_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_r_450_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v_impl_594_; lean_object* v___x_595_; 
lean_dec(v_size_446_);
v_impl_594_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_443_, v_v_444_, v_l_449_);
v___x_595_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_450_) == 0)
{
lean_object* v_size_596_; lean_object* v_size_597_; lean_object* v_k_598_; lean_object* v_v_599_; lean_object* v_l_600_; lean_object* v_r_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_size_596_ = lean_ctor_get(v_r_450_, 0);
v_size_597_ = lean_ctor_get(v_impl_594_, 0);
lean_inc(v_size_597_);
v_k_598_ = lean_ctor_get(v_impl_594_, 1);
lean_inc(v_k_598_);
v_v_599_ = lean_ctor_get(v_impl_594_, 2);
lean_inc(v_v_599_);
v_l_600_ = lean_ctor_get(v_impl_594_, 3);
lean_inc(v_l_600_);
v_r_601_ = lean_ctor_get(v_impl_594_, 4);
lean_inc(v_r_601_);
v___x_602_ = lean_unsigned_to_nat(3u);
v___x_603_ = lean_nat_mul(v___x_602_, v_size_596_);
v___x_604_ = lean_nat_dec_lt(v___x_603_, v_size_597_);
lean_dec(v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec(v_r_601_);
lean_dec(v_l_600_);
lean_dec(v_v_599_);
lean_dec(v_k_598_);
v___x_605_ = lean_nat_add(v___x_595_, v_size_597_);
lean_dec(v_size_597_);
v___x_606_ = lean_nat_add(v___x_605_, v_size_596_);
lean_dec(v___x_605_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 3, v_impl_594_);
lean_ctor_set(v___x_452_, 0, v___x_606_);
v___x_608_ = v___x_452_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_impl_594_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_r_450_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_675_; 
v_isSharedCheck_675_ = !lean_is_exclusive(v_impl_594_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_676_ = lean_ctor_get(v_impl_594_, 4);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_impl_594_, 3);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_impl_594_, 2);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_impl_594_, 1);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_impl_594_, 0);
lean_dec(v_unused_680_);
v___x_611_ = v_impl_594_;
v_isShared_612_ = v_isSharedCheck_675_;
goto v_resetjp_610_;
}
else
{
lean_dec(v_impl_594_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_675_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_size_613_; lean_object* v_size_614_; lean_object* v_k_615_; lean_object* v_v_616_; lean_object* v_l_617_; lean_object* v_r_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_size_613_ = lean_ctor_get(v_l_600_, 0);
v_size_614_ = lean_ctor_get(v_r_601_, 0);
v_k_615_ = lean_ctor_get(v_r_601_, 1);
v_v_616_ = lean_ctor_get(v_r_601_, 2);
v_l_617_ = lean_ctor_get(v_r_601_, 3);
v_r_618_ = lean_ctor_get(v_r_601_, 4);
v___x_619_ = lean_unsigned_to_nat(2u);
v___x_620_ = lean_nat_mul(v___x_619_, v_size_613_);
v___x_621_ = lean_nat_dec_lt(v_size_614_, v___x_620_);
lean_dec(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_650_; 
lean_inc(v_r_618_);
lean_inc(v_l_617_);
lean_inc(v_v_616_);
lean_inc(v_k_615_);
v_isSharedCheck_650_ = !lean_is_exclusive(v_r_601_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; 
v_unused_651_ = lean_ctor_get(v_r_601_, 4);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_r_601_, 3);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_r_601_, 2);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_r_601_, 1);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_r_601_, 0);
lean_dec(v_unused_655_);
v___x_623_ = v_r_601_;
v_isShared_624_ = v_isSharedCheck_650_;
goto v_resetjp_622_;
}
else
{
lean_dec(v_r_601_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_650_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___x_638_; lean_object* v___y_640_; 
v___x_625_ = lean_nat_add(v___x_595_, v_size_597_);
lean_dec(v_size_597_);
v___x_626_ = lean_nat_add(v___x_625_, v_size_596_);
lean_dec(v___x_625_);
v___x_638_ = lean_nat_add(v___x_595_, v_size_613_);
if (lean_obj_tag(v_l_617_) == 0)
{
lean_object* v_size_648_; 
v_size_648_ = lean_ctor_get(v_l_617_, 0);
lean_inc(v_size_648_);
v___y_640_ = v_size_648_;
goto v___jp_639_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___y_640_ = v___x_649_;
goto v___jp_639_;
}
v___jp_627_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_nat_add(v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec(v___y_629_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v_r_450_);
lean_ctor_set(v___x_623_, 3, v_r_618_);
lean_ctor_set(v___x_623_, 2, v_v_448_);
lean_ctor_set(v___x_623_, 1, v_k_447_);
lean_ctor_set(v___x_623_, 0, v___x_631_);
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_r_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_r_450_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v___x_633_);
lean_ctor_set(v___x_611_, 3, v___y_628_);
lean_ctor_set(v___x_611_, 2, v_v_616_);
lean_ctor_set(v___x_611_, 1, v_k_615_);
lean_ctor_set(v___x_611_, 0, v___x_626_);
v___x_635_ = v___x_611_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_615_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_616_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v___y_628_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_nat_add(v___x_638_, v___y_640_);
lean_dec(v___y_640_);
lean_dec(v___x_638_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_l_617_);
lean_ctor_set(v___x_452_, 3, v_l_600_);
lean_ctor_set(v___x_452_, 2, v_v_599_);
lean_ctor_set(v___x_452_, 1, v_k_598_);
lean_ctor_set(v___x_452_, 0, v___x_641_);
v___x_643_ = v___x_452_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_v_599_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_l_600_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_l_617_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = lean_nat_add(v___x_595_, v_size_596_);
if (lean_obj_tag(v_r_618_) == 0)
{
lean_object* v_size_645_; 
v_size_645_ = lean_ctor_get(v_r_618_, 0);
lean_inc(v_size_645_);
v___y_628_ = v___x_643_;
v___y_629_ = v___x_644_;
v___y_630_ = v_size_645_;
goto v___jp_627_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___y_628_ = v___x_643_;
v___y_629_ = v___x_644_;
v___y_630_ = v___x_646_;
goto v___jp_627_;
}
}
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
lean_del_object(v___x_452_);
v___x_656_ = lean_nat_add(v___x_595_, v_size_597_);
lean_dec(v_size_597_);
v___x_657_ = lean_nat_add(v___x_656_, v_size_596_);
lean_dec(v___x_656_);
v___x_658_ = lean_nat_add(v___x_595_, v_size_596_);
v___x_659_ = lean_nat_add(v___x_658_, v_size_614_);
lean_dec(v___x_658_);
lean_inc_ref(v_r_450_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v_r_450_);
lean_ctor_set(v___x_611_, 3, v_r_601_);
lean_ctor_set(v___x_611_, 2, v_v_448_);
lean_ctor_set(v___x_611_, 1, v_k_447_);
lean_ctor_set(v___x_611_, 0, v___x_659_);
v___x_661_ = v___x_611_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_r_601_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_r_450_);
v___x_661_ = v_reuseFailAlloc_674_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_isSharedCheck_668_ = !lean_is_exclusive(v_r_450_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; lean_object* v_unused_673_; 
v_unused_669_ = lean_ctor_get(v_r_450_, 4);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_r_450_, 3);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_r_450_, 2);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_r_450_, 1);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_r_450_, 0);
lean_dec(v_unused_673_);
v___x_663_ = v_r_450_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_dec(v_r_450_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 4, v___x_661_);
lean_ctor_set(v___x_663_, 3, v_l_600_);
lean_ctor_set(v___x_663_, 2, v_v_599_);
lean_ctor_set(v___x_663_, 1, v_k_598_);
lean_ctor_set(v___x_663_, 0, v___x_657_);
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_v_599_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_l_600_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v___x_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_681_; 
v_l_681_ = lean_ctor_get(v_impl_594_, 3);
lean_inc(v_l_681_);
if (lean_obj_tag(v_l_681_) == 0)
{
lean_object* v_r_682_; lean_object* v_k_683_; lean_object* v_v_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_695_; 
v_r_682_ = lean_ctor_get(v_impl_594_, 4);
v_k_683_ = lean_ctor_get(v_impl_594_, 1);
v_v_684_ = lean_ctor_get(v_impl_594_, 2);
v_isSharedCheck_695_ = !lean_is_exclusive(v_impl_594_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_696_ = lean_ctor_get(v_impl_594_, 3);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_impl_594_, 0);
lean_dec(v_unused_697_);
v___x_686_ = v_impl_594_;
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_r_682_);
lean_inc(v_v_684_);
lean_inc(v_k_683_);
lean_dec(v_impl_594_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_682_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 3, v_r_682_);
lean_ctor_set(v___x_686_, 2, v_v_448_);
lean_ctor_set(v___x_686_, 1, v_k_447_);
lean_ctor_set(v___x_686_, 0, v___x_595_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_r_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_r_682_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v___x_690_);
lean_ctor_set(v___x_452_, 3, v_l_681_);
lean_ctor_set(v___x_452_, 2, v_v_684_);
lean_ctor_set(v___x_452_, 1, v_k_683_);
lean_ctor_set(v___x_452_, 0, v___x_688_);
v___x_692_ = v___x_452_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_l_681_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_r_698_; 
v_r_698_ = lean_ctor_get(v_impl_594_, 4);
lean_inc(v_r_698_);
if (lean_obj_tag(v_r_698_) == 0)
{
lean_object* v_k_699_; lean_object* v_v_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_723_; 
v_k_699_ = lean_ctor_get(v_impl_594_, 1);
v_v_700_ = lean_ctor_get(v_impl_594_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_impl_594_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; 
v_unused_724_ = lean_ctor_get(v_impl_594_, 4);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_impl_594_, 3);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_impl_594_, 0);
lean_dec(v_unused_726_);
v___x_702_ = v_impl_594_;
v_isShared_703_ = v_isSharedCheck_723_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_v_700_);
lean_inc(v_k_699_);
lean_dec(v_impl_594_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_723_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_k_704_; lean_object* v_v_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_719_; 
v_k_704_ = lean_ctor_get(v_r_698_, 1);
v_v_705_ = lean_ctor_get(v_r_698_, 2);
v_isSharedCheck_719_ = !lean_is_exclusive(v_r_698_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; 
v_unused_720_ = lean_ctor_get(v_r_698_, 4);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_r_698_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_r_698_, 0);
lean_dec(v_unused_722_);
v___x_707_ = v_r_698_;
v_isShared_708_ = v_isSharedCheck_719_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_v_705_);
lean_inc(v_k_704_);
lean_dec(v_r_698_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_719_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_unsigned_to_nat(3u);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 4, v_l_681_);
lean_ctor_set(v___x_707_, 3, v_l_681_);
lean_ctor_set(v___x_707_, 2, v_v_700_);
lean_ctor_set(v___x_707_, 1, v_k_699_);
lean_ctor_set(v___x_707_, 0, v___x_595_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_k_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_v_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_l_681_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_l_681_);
v___x_711_ = v_reuseFailAlloc_718_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_l_681_);
lean_ctor_set(v___x_702_, 2, v_v_448_);
lean_ctor_set(v___x_702_, 1, v_k_447_);
lean_ctor_set(v___x_702_, 0, v___x_595_);
v___x_713_ = v___x_702_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_l_681_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_l_681_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v___x_713_);
lean_ctor_set(v___x_452_, 3, v___x_711_);
lean_ctor_set(v___x_452_, 2, v_v_705_);
lean_ctor_set(v___x_452_, 1, v_k_704_);
lean_ctor_set(v___x_452_, 0, v___x_709_);
v___x_715_ = v___x_452_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_704_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_705_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_unsigned_to_nat(2u);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_r_698_);
lean_ctor_set(v___x_452_, 3, v_impl_594_);
lean_ctor_set(v___x_452_, 0, v___x_727_);
v___x_729_ = v___x_452_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_447_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_448_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_impl_594_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_r_698_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v_k_443_);
lean_ctor_set(v___x_733_, 2, v_v_444_);
lean_ctor_set(v___x_733_, 3, v_t_445_);
lean_ctor_set(v___x_733_, 4, v_t_445_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(lean_object* v_t_734_, lean_object* v_k_735_){
_start:
{
if (lean_obj_tag(v_t_734_) == 0)
{
lean_object* v_k_736_; lean_object* v_v_737_; lean_object* v_l_738_; lean_object* v_r_739_; uint8_t v___x_740_; 
v_k_736_ = lean_ctor_get(v_t_734_, 1);
v_v_737_ = lean_ctor_get(v_t_734_, 2);
v_l_738_ = lean_ctor_get(v_t_734_, 3);
v_r_739_ = lean_ctor_get(v_t_734_, 4);
v___x_740_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_735_, v_k_736_);
switch(v___x_740_)
{
case 0:
{
v_t_734_ = v_l_738_;
goto _start;
}
case 1:
{
lean_object* v___x_742_; 
lean_inc(v_v_737_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_v_737_);
return v___x_742_;
}
default: 
{
v_t_734_ = v_r_739_;
goto _start;
}
}
}
else
{
lean_object* v___x_744_; 
v___x_744_ = lean_box(0);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg___boxed(lean_object* v_t_745_, lean_object* v_k_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_745_, v_k_746_);
lean_dec(v_k_746_);
lean_dec(v_t_745_);
return v_res_747_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(lean_object* v_k_748_, lean_object* v_t_749_){
_start:
{
if (lean_obj_tag(v_t_749_) == 0)
{
lean_object* v_k_750_; lean_object* v_l_751_; lean_object* v_r_752_; uint8_t v___x_753_; 
v_k_750_ = lean_ctor_get(v_t_749_, 1);
v_l_751_ = lean_ctor_get(v_t_749_, 3);
v_r_752_ = lean_ctor_get(v_t_749_, 4);
v___x_753_ = lean_nat_dec_lt(v_k_748_, v_k_750_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; 
v___x_754_ = lean_nat_dec_eq(v_k_748_, v_k_750_);
if (v___x_754_ == 0)
{
v_t_749_ = v_r_752_;
goto _start;
}
else
{
return v___x_754_;
}
}
else
{
v_t_749_ = v_l_751_;
goto _start;
}
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg___boxed(lean_object* v_k_758_, lean_object* v_t_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_758_, v_t_759_);
lean_dec(v_t_759_);
lean_dec(v_k_758_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(lean_object* v_localInst2Index_762_, lean_object* v_e_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_fvarId_766_; lean_object* v___x_767_; 
v_fvarId_766_ = l_Lean_Expr_fvarId_x21(v_e_763_);
v___x_767_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_localInst2Index_762_, v_fvarId_766_);
lean_dec(v_fvarId_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_768_; 
v___x_768_ = lean_box(0);
return v___x_768_;
}
else
{
lean_object* v_val_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___y_773_; uint8_t v___x_775_; 
v_val_769_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_val_769_);
lean_dec_ref(v___x_767_);
v___x_770_ = lean_st_ref_take(v___y_764_);
v___x_771_ = lean_box(0);
v___x_775_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_val_769_, v___x_770_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_val_769_, v___x_771_, v___x_770_);
v___y_773_ = v___x_776_;
goto v___jp_772_;
}
else
{
lean_dec(v_val_769_);
v___y_773_ = v___x_770_;
goto v___jp_772_;
}
v___jp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_st_ref_set(v___y_764_, v___y_773_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed(lean_object* v_localInst2Index_777_, lean_object* v_e_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0(v_localInst2Index_777_, v_e_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v_e_778_);
lean_dec(v_localInst2Index_777_);
return v_res_781_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_a_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
uint8_t v___x_784_; 
v___x_784_ = 0;
return v___x_784_;
}
else
{
lean_object* v_key_785_; lean_object* v_tail_786_; uint8_t v___x_787_; 
v_key_785_ = lean_ctor_get(v_x_783_, 0);
v_tail_786_ = lean_ctor_get(v_x_783_, 2);
v___x_787_ = lean_expr_eqv(v_key_785_, v_a_782_);
if (v___x_787_ == 0)
{
v_x_783_ = v_tail_786_;
goto _start;
}
else
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_a_789_, lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec_ref(v_a_789_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
return v_x_793_;
}
else
{
lean_object* v_key_795_; lean_object* v_value_796_; lean_object* v_tail_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_820_; 
v_key_795_ = lean_ctor_get(v_x_794_, 0);
v_value_796_ = lean_ctor_get(v_x_794_, 1);
v_tail_797_ = lean_ctor_get(v_x_794_, 2);
v_isSharedCheck_820_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_820_ == 0)
{
v___x_799_ = v_x_794_;
v_isShared_800_ = v_isSharedCheck_820_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_tail_797_);
lean_inc(v_value_796_);
lean_inc(v_key_795_);
lean_dec(v_x_794_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_820_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; uint64_t v___x_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v_fold_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_801_ = lean_array_get_size(v_x_793_);
v___x_802_ = l_Lean_Expr_hash(v_key_795_);
v___x_803_ = 32ULL;
v___x_804_ = lean_uint64_shift_right(v___x_802_, v___x_803_);
v_fold_805_ = lean_uint64_xor(v___x_802_, v___x_804_);
v___x_806_ = 16ULL;
v___x_807_ = lean_uint64_shift_right(v_fold_805_, v___x_806_);
v___x_808_ = lean_uint64_xor(v_fold_805_, v___x_807_);
v___x_809_ = lean_uint64_to_usize(v___x_808_);
v___x_810_ = lean_usize_of_nat(v___x_801_);
v___x_811_ = ((size_t)1ULL);
v___x_812_ = lean_usize_sub(v___x_810_, v___x_811_);
v___x_813_ = lean_usize_land(v___x_809_, v___x_812_);
v___x_814_ = lean_array_uget_borrowed(v_x_793_, v___x_813_);
lean_inc(v___x_814_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 2, v___x_814_);
v___x_816_ = v___x_799_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_key_795_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_value_796_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v___x_814_);
v___x_816_ = v_reuseFailAlloc_819_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_array_uset(v_x_793_, v___x_813_, v___x_816_);
v_x_793_ = v___x_817_;
v_x_794_ = v_tail_797_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_i_821_, lean_object* v_source_822_, lean_object* v_target_823_){
_start:
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_array_get_size(v_source_822_);
v___x_825_ = lean_nat_dec_lt(v_i_821_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec_ref(v_source_822_);
lean_dec(v_i_821_);
return v_target_823_;
}
else
{
lean_object* v_es_826_; lean_object* v___x_827_; lean_object* v_source_828_; lean_object* v_target_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_es_826_ = lean_array_fget(v_source_822_, v_i_821_);
v___x_827_ = lean_box(0);
v_source_828_ = lean_array_fset(v_source_822_, v_i_821_, v___x_827_);
v_target_829_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_target_823_, v_es_826_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_i_821_, v___x_830_);
lean_dec(v_i_821_);
v_i_821_ = v___x_831_;
v_source_822_ = v_source_828_;
v_target_823_ = v_target_829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_data_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_nbuckets_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_834_ = lean_array_get_size(v_data_833_);
v___x_835_ = lean_unsigned_to_nat(2u);
v_nbuckets_836_ = lean_nat_mul(v___x_834_, v___x_835_);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_box(0);
v___x_839_ = lean_mk_array(v_nbuckets_836_, v___x_838_);
v___x_840_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v___x_837_, v_data_833_, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(lean_object* v_m_841_, lean_object* v_a_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_size_844_; lean_object* v_buckets_845_; lean_object* v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v_fold_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v_bkt_859_; uint8_t v___x_860_; 
v_size_844_ = lean_ctor_get(v_m_841_, 0);
v_buckets_845_ = lean_ctor_get(v_m_841_, 1);
v___x_846_ = lean_array_get_size(v_buckets_845_);
v___x_847_ = l_Lean_Expr_hash(v_a_842_);
v___x_848_ = 32ULL;
v___x_849_ = lean_uint64_shift_right(v___x_847_, v___x_848_);
v_fold_850_ = lean_uint64_xor(v___x_847_, v___x_849_);
v___x_851_ = 16ULL;
v___x_852_ = lean_uint64_shift_right(v_fold_850_, v___x_851_);
v___x_853_ = lean_uint64_xor(v_fold_850_, v___x_852_);
v___x_854_ = lean_uint64_to_usize(v___x_853_);
v___x_855_ = lean_usize_of_nat(v___x_846_);
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_sub(v___x_855_, v___x_856_);
v___x_858_ = lean_usize_land(v___x_854_, v___x_857_);
v_bkt_859_ = lean_array_uget_borrowed(v_buckets_845_, v___x_858_);
v___x_860_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_842_, v_bkt_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_881_; 
lean_inc_ref(v_buckets_845_);
lean_inc(v_size_844_);
v_isSharedCheck_881_ = !lean_is_exclusive(v_m_841_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_882_ = lean_ctor_get(v_m_841_, 1);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_m_841_, 0);
lean_dec(v_unused_883_);
v___x_862_ = v_m_841_;
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
else
{
lean_dec(v_m_841_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v_size_x27_865_; lean_object* v___x_866_; lean_object* v_buckets_x27_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_864_ = lean_unsigned_to_nat(1u);
v_size_x27_865_ = lean_nat_add(v_size_844_, v___x_864_);
lean_dec(v_size_844_);
lean_inc(v_bkt_859_);
v___x_866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_866_, 0, v_a_842_);
lean_ctor_set(v___x_866_, 1, v_b_843_);
lean_ctor_set(v___x_866_, 2, v_bkt_859_);
v_buckets_x27_867_ = lean_array_uset(v_buckets_845_, v___x_858_, v___x_866_);
v___x_868_ = lean_unsigned_to_nat(4u);
v___x_869_ = lean_nat_mul(v_size_x27_865_, v___x_868_);
v___x_870_ = lean_unsigned_to_nat(3u);
v___x_871_ = lean_nat_div(v___x_869_, v___x_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_array_get_size(v_buckets_x27_867_);
v___x_873_ = lean_nat_dec_le(v___x_871_, v___x_872_);
lean_dec(v___x_871_);
if (v___x_873_ == 0)
{
lean_object* v_val_874_; lean_object* v___x_876_; 
v_val_874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_buckets_x27_867_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_val_874_);
lean_ctor_set(v___x_862_, 0, v_size_x27_865_);
v___x_876_ = v___x_862_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_size_x27_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_val_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_object* v___x_879_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_buckets_x27_867_);
lean_ctor_set(v___x_862_, 0, v_size_x27_865_);
v___x_879_ = v___x_862_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_size_x27_865_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_buckets_x27_867_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_dec(v_b_843_);
lean_dec_ref(v_a_842_);
return v_m_841_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(lean_object* v_m_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_buckets_886_; lean_object* v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v_fold_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v_buckets_886_ = lean_ctor_get(v_m_884_, 1);
v___x_887_ = lean_array_get_size(v_buckets_886_);
v___x_888_ = l_Lean_Expr_hash(v_a_885_);
v___x_889_ = 32ULL;
v___x_890_ = lean_uint64_shift_right(v___x_888_, v___x_889_);
v_fold_891_ = lean_uint64_xor(v___x_888_, v___x_890_);
v___x_892_ = 16ULL;
v___x_893_ = lean_uint64_shift_right(v_fold_891_, v___x_892_);
v___x_894_ = lean_uint64_xor(v_fold_891_, v___x_893_);
v___x_895_ = lean_uint64_to_usize(v___x_894_);
v___x_896_ = lean_usize_of_nat(v___x_887_);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_sub(v___x_896_, v___x_897_);
v___x_899_ = lean_usize_land(v___x_895_, v___x_898_);
v___x_900_ = lean_array_uget_borrowed(v_buckets_886_, v___x_899_);
v___x_901_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_885_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_m_902_, lean_object* v_a_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_902_, v_a_903_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v_m_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(lean_object* v_e_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; lean_object* v_checked_910_; uint8_t v___x_911_; 
v___x_909_ = lean_st_ref_get(v_a_907_);
v_checked_910_ = lean_ctor_get(v___x_909_, 1);
lean_inc_ref(v_checked_910_);
lean_dec(v___x_909_);
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_checked_910_, v_e_906_);
lean_dec_ref(v_checked_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v_visited_913_; lean_object* v_checked_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_924_; 
v___x_912_ = lean_st_ref_take(v_a_907_);
v_visited_913_ = lean_ctor_get(v___x_912_, 0);
v_checked_914_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_924_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_checked_914_);
lean_inc(v_visited_913_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_918_ = lean_box(0);
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_checked_914_, v_e_906_, v___x_918_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v___x_919_);
v___x_921_ = v___x_916_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_visited_913_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_923_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; 
v___x_922_ = lean_st_ref_set(v_a_907_, v___x_921_);
return v___x_911_;
}
}
}
else
{
lean_dec_ref(v_e_906_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_e_925_, lean_object* v_a_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_925_, v_a_926_);
lean_dec(v_a_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_930_; size_t v___x_931_; size_t v___x_932_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = ((size_t)8192ULL);
v___x_932_ = lean_usize_sub(v___x_931_, v___x_930_);
return v___x_932_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(lean_object* v_e_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; lean_object* v_visited_937_; size_t v___x_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; size_t v___x_942_; uint8_t v___x_943_; 
v___x_936_ = lean_st_ref_get(v_a_934_);
v_visited_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_visited_937_);
lean_dec(v___x_936_);
v___x_938_ = lean_ptr_addr(v_e_933_);
v___x_939_ = lean_usize_once(&l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_940_ = lean_usize_mod(v___x_938_, v___x_939_);
v___x_941_ = lean_array_uget(v_visited_937_, v___x_940_);
lean_dec_ref(v_visited_937_);
v___x_942_ = lean_ptr_addr(v___x_941_);
lean_dec(v___x_941_);
v___x_943_ = lean_usize_dec_eq(v___x_942_, v___x_938_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v_visited_945_; lean_object* v_checked_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_955_; 
v___x_944_ = lean_st_ref_take(v_a_934_);
v_visited_945_ = lean_ctor_get(v___x_944_, 0);
v_checked_946_ = lean_ctor_get(v___x_944_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_955_ == 0)
{
v___x_948_ = v___x_944_;
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_checked_946_);
lean_inc(v_visited_945_);
lean_dec(v___x_944_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_array_uset(v_visited_945_, v___x_940_, v_e_933_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_checked_946_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; 
v___x_953_ = lean_st_ref_set(v_a_934_, v___x_952_);
return v___x_943_;
}
}
}
else
{
lean_dec_ref(v_e_933_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_e_956_, lean_object* v_a_957_, lean_object* v___y_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_956_, v_a_957_);
lean_dec(v_a_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(lean_object* v_p_961_, lean_object* v_f_962_, uint8_t v_stopWhenVisited_963_, lean_object* v_e_964_, lean_object* v_a_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___y_969_; lean_object* v_d_970_; lean_object* v_b_971_; lean_object* v___y_972_; lean_object* v___y_976_; lean_object* v___y_977_; uint8_t v___x_997_; 
lean_inc_ref(v_e_964_);
v___x_997_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_964_, v_a_965_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; uint8_t v___x_999_; 
lean_inc_ref(v_p_961_);
lean_inc_ref(v_e_964_);
v___x_998_ = lean_apply_1(v_p_961_, v_e_964_);
v___x_999_ = lean_unbox(v___x_998_);
if (v___x_999_ == 0)
{
v___y_976_ = v_a_965_;
v___y_977_ = v___y_966_;
goto v___jp_975_;
}
else
{
uint8_t v___x_1000_; 
lean_inc_ref(v_e_964_);
v___x_1000_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_964_, v_a_965_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_inc_ref(v_f_962_);
lean_inc(v___y_966_);
lean_inc_ref(v_e_964_);
v___x_1001_ = lean_apply_3(v_f_962_, v_e_964_, v___y_966_, lean_box(0));
if (v_stopWhenVisited_963_ == 0)
{
v___y_976_ = v_a_965_;
v___y_977_ = v___y_966_;
goto v___jp_975_;
}
else
{
lean_object* v___x_1002_; 
lean_dec_ref(v_e_964_);
lean_dec_ref(v_f_962_);
lean_dec_ref(v_p_961_);
v___x_1002_ = lean_box(0);
return v___x_1002_;
}
}
else
{
v___y_976_ = v_a_965_;
v___y_977_ = v___y_966_;
goto v___jp_975_;
}
}
}
else
{
lean_object* v___x_1003_; 
lean_dec_ref(v_e_964_);
lean_dec_ref(v_f_962_);
lean_dec_ref(v_p_961_);
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
v___jp_968_:
{
lean_object* v___x_973_; 
lean_inc_ref(v_f_962_);
lean_inc_ref(v_p_961_);
v___x_973_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_961_, v_f_962_, v_stopWhenVisited_963_, v_d_970_, v___y_972_, v___y_969_);
v_e_964_ = v_b_971_;
v_a_965_ = v___y_972_;
v___y_966_ = v___y_969_;
goto _start;
}
v___jp_975_:
{
switch(lean_obj_tag(v_e_964_))
{
case 7:
{
lean_object* v_binderType_978_; lean_object* v_body_979_; 
v_binderType_978_ = lean_ctor_get(v_e_964_, 1);
lean_inc_ref(v_binderType_978_);
v_body_979_ = lean_ctor_get(v_e_964_, 2);
lean_inc_ref(v_body_979_);
lean_dec_ref(v_e_964_);
v___y_969_ = v___y_977_;
v_d_970_ = v_binderType_978_;
v_b_971_ = v_body_979_;
v___y_972_ = v___y_976_;
goto v___jp_968_;
}
case 6:
{
lean_object* v_binderType_980_; lean_object* v_body_981_; 
v_binderType_980_ = lean_ctor_get(v_e_964_, 1);
lean_inc_ref(v_binderType_980_);
v_body_981_ = lean_ctor_get(v_e_964_, 2);
lean_inc_ref(v_body_981_);
lean_dec_ref(v_e_964_);
v___y_969_ = v___y_977_;
v_d_970_ = v_binderType_980_;
v_b_971_ = v_body_981_;
v___y_972_ = v___y_976_;
goto v___jp_968_;
}
case 8:
{
lean_object* v_type_982_; lean_object* v_value_983_; lean_object* v_body_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_type_982_ = lean_ctor_get(v_e_964_, 1);
lean_inc_ref(v_type_982_);
v_value_983_ = lean_ctor_get(v_e_964_, 2);
lean_inc_ref(v_value_983_);
v_body_984_ = lean_ctor_get(v_e_964_, 3);
lean_inc_ref(v_body_984_);
lean_dec_ref(v_e_964_);
lean_inc_ref_n(v_f_962_, 2);
lean_inc_ref_n(v_p_961_, 2);
v___x_985_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_961_, v_f_962_, v_stopWhenVisited_963_, v_type_982_, v___y_976_, v___y_977_);
v___x_986_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_961_, v_f_962_, v_stopWhenVisited_963_, v_value_983_, v___y_976_, v___y_977_);
v_e_964_ = v_body_984_;
v_a_965_ = v___y_976_;
v___y_966_ = v___y_977_;
goto _start;
}
case 5:
{
lean_object* v_fn_988_; lean_object* v_arg_989_; lean_object* v___x_990_; 
v_fn_988_ = lean_ctor_get(v_e_964_, 0);
lean_inc_ref(v_fn_988_);
v_arg_989_ = lean_ctor_get(v_e_964_, 1);
lean_inc_ref(v_arg_989_);
lean_dec_ref(v_e_964_);
lean_inc_ref(v_f_962_);
lean_inc_ref(v_p_961_);
v___x_990_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_961_, v_f_962_, v_stopWhenVisited_963_, v_fn_988_, v___y_976_, v___y_977_);
v_e_964_ = v_arg_989_;
v_a_965_ = v___y_976_;
v___y_966_ = v___y_977_;
goto _start;
}
case 10:
{
lean_object* v_expr_992_; 
v_expr_992_ = lean_ctor_get(v_e_964_, 1);
lean_inc_ref(v_expr_992_);
lean_dec_ref(v_e_964_);
v_e_964_ = v_expr_992_;
v_a_965_ = v___y_976_;
v___y_966_ = v___y_977_;
goto _start;
}
case 11:
{
lean_object* v_struct_994_; 
v_struct_994_ = lean_ctor_get(v_e_964_, 2);
lean_inc_ref(v_struct_994_);
lean_dec_ref(v_e_964_);
v_e_964_ = v_struct_994_;
v_a_965_ = v___y_976_;
v___y_966_ = v___y_977_;
goto _start;
}
default: 
{
lean_object* v___x_996_; 
lean_dec_ref(v_e_964_);
lean_dec_ref(v_f_962_);
lean_dec_ref(v_p_961_);
v___x_996_ = lean_box(0);
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg___boxed(lean_object* v_p_1004_, lean_object* v_f_1005_, lean_object* v_stopWhenVisited_1006_, lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1011_; lean_object* v_res_1012_; 
v_stopWhenVisited_boxed_1011_ = lean_unbox(v_stopWhenVisited_1006_);
v_res_1012_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1004_, v_f_1005_, v_stopWhenVisited_boxed_1011_, v_e_1007_, v_a_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec(v_a_1008_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(lean_object* v_p_1013_, lean_object* v_f_1014_, lean_object* v_e_1015_, uint8_t v_stopWhenVisited_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1019_ = l_Lean_ForEachExprWhere_initCache;
v___x_1020_ = lean_st_mk_ref(v___x_1019_);
v___x_1021_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1013_, v_f_1014_, v_stopWhenVisited_1016_, v_e_1015_, v___x_1020_, v___y_1017_);
v___x_1022_ = lean_st_ref_get(v___x_1020_);
lean_dec(v___x_1020_);
lean_dec(v___x_1022_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg___boxed(lean_object* v_p_1023_, lean_object* v_f_1024_, lean_object* v_e_1025_, lean_object* v_stopWhenVisited_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1029_; lean_object* v_res_1030_; 
v_stopWhenVisited_boxed_1029_ = lean_unbox(v_stopWhenVisited_1026_);
v_res_1030_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1023_, v_f_1024_, v_e_1025_, v_stopWhenVisited_boxed_1029_, v___y_1027_);
lean_dec(v___y_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(lean_object* v_usedInstIdxs_1032_, lean_object* v___f_1033_, lean_object* v_e_1034_, uint8_t v___x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1038_ = lean_st_mk_ref(v_usedInstIdxs_1032_);
v___x_1039_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0));
v___x_1040_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v___x_1039_, v___f_1033_, v_e_1034_, v___x_1035_, v___x_1038_);
v___x_1041_ = lean_st_ref_get(v___x_1038_);
lean_dec(v___x_1038_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed(lean_object* v_usedInstIdxs_1043_, lean_object* v___f_1044_, lean_object* v_e_1045_, lean_object* v___x_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v___x_7006__boxed_1049_; lean_object* v_res_1050_; 
v___x_7006__boxed_1049_ = lean_unbox(v___x_1046_);
v_res_1050_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(v_usedInstIdxs_1043_, v___f_1044_, v_e_1045_, v___x_7006__boxed_1049_, v_x_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(lean_object* v_usedInstIdxs_1051_, lean_object* v_localInst2Index_1052_, lean_object* v_e_1053_){
_start:
{
if (lean_obj_tag(v_localInst2Index_1052_) == 0)
{
lean_object* v___f_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v_snd_1059_; 
v___f_1054_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1054_, 0, v_localInst2Index_1052_);
v___x_1055_ = 0;
v___x_1056_ = lean_box(v___x_1055_);
v___f_1057_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1057_, 0, v_usedInstIdxs_1051_);
lean_closure_set(v___f_1057_, 1, v___f_1054_);
lean_closure_set(v___f_1057_, 2, v_e_1053_);
lean_closure_set(v___f_1057_, 3, v___x_1056_);
v___x_1058_ = l_runST___redArg(v___f_1057_);
v_snd_1059_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_snd_1059_);
lean_dec(v___x_1058_);
return v_snd_1059_;
}
else
{
lean_dec_ref(v_e_1053_);
return v_usedInstIdxs_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(lean_object* v_00_u03b4_1060_, lean_object* v_t_1061_, lean_object* v_k_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_1061_, v_k_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___boxed(lean_object* v_00_u03b4_1064_, lean_object* v_t_1065_, lean_object* v_k_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(v_00_u03b4_1064_, v_t_1065_, v_k_1066_);
lean_dec(v_k_1066_);
lean_dec(v_t_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(lean_object* v_00_u03b2_1068_, lean_object* v_k_1069_, lean_object* v_t_1070_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_1069_, v_t_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_k_1073_, lean_object* v_t_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(v_00_u03b2_1072_, v_k_1073_, v_t_1074_);
lean_dec(v_t_1074_);
lean_dec(v_k_1073_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2(lean_object* v_00_u03b2_1077_, lean_object* v_k_1078_, lean_object* v_v_1079_, lean_object* v_t_1080_, lean_object* v_hl_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_1078_, v_v_1079_, v_t_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(lean_object* v_x_1083_, lean_object* v_p_1084_, lean_object* v_f_1085_, lean_object* v_e_1086_, uint8_t v_stopWhenVisited_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1084_, v_f_1085_, v_e_1086_, v_stopWhenVisited_1087_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___boxed(lean_object* v_x_1091_, lean_object* v_p_1092_, lean_object* v_f_1093_, lean_object* v_e_1094_, lean_object* v_stopWhenVisited_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1098_; lean_object* v_res_1099_; 
v_stopWhenVisited_boxed_1098_ = lean_unbox(v_stopWhenVisited_1095_);
v_res_1099_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(v_x_1091_, v_p_1092_, v_f_1093_, v_e_1094_, v_stopWhenVisited_boxed_1098_, v___y_1096_);
lean_dec(v___y_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(lean_object* v_x_1100_, lean_object* v_e_1101_, lean_object* v_a_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_1101_, v_a_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___boxed(lean_object* v_x_1106_, lean_object* v_e_1107_, lean_object* v_a_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(v_x_1106_, v_e_1107_, v_a_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec(v_a_1108_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(lean_object* v_x_1113_, lean_object* v_p_1114_, lean_object* v_f_1115_, uint8_t v_stopWhenVisited_1116_, lean_object* v_e_1117_, lean_object* v_a_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1114_, v_f_1115_, v_stopWhenVisited_1116_, v_e_1117_, v_a_1118_, v___y_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___boxed(lean_object* v_x_1122_, lean_object* v_p_1123_, lean_object* v_f_1124_, lean_object* v_stopWhenVisited_1125_, lean_object* v_e_1126_, lean_object* v_a_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1130_; lean_object* v_res_1131_; 
v_stopWhenVisited_boxed_1130_ = lean_unbox(v_stopWhenVisited_1125_);
v_res_1131_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(v_x_1122_, v_p_1123_, v_f_1124_, v_stopWhenVisited_boxed_1130_, v_e_1126_, v_a_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec(v_a_1127_);
return v_res_1131_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(lean_object* v_x_1132_, lean_object* v_e_1133_, lean_object* v_a_1134_, lean_object* v___y_1135_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_1133_, v_a_1134_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___boxed(lean_object* v_x_1138_, lean_object* v_e_1139_, lean_object* v_a_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_res_1143_; lean_object* v_r_1144_; 
v_res_1143_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(v_x_1138_, v_e_1139_, v_a_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec(v_a_1140_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1145_, lean_object* v_m_1146_, lean_object* v_a_1147_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_1146_, v_a_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_m_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(v_00_u03b2_1149_, v_m_1150_, v_a_1151_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_m_1150_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1154_, lean_object* v_m_1155_, lean_object* v_a_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_m_1155_, v_a_1156_, v_b_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1159_, lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_1160_, v_x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1163_, lean_object* v_a_1164_, lean_object* v_x_1165_){
_start:
{
uint8_t v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(v_00_u03b2_1163_, v_a_1164_, v_x_1165_);
lean_dec(v_x_1165_);
lean_dec_ref(v_a_1164_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_1168_, lean_object* v_data_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_data_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1171_, lean_object* v_i_1172_, lean_object* v_source_1173_, lean_object* v_target_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_i_1172_, v_source_1173_, v_target_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11(lean_object* v_00_u03b2_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_x_1177_, v_x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Array_mkArray0(lean_box(0));
return v___x_1196_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0));
v___x_1212_ = l_String_toRawSubstring_x27(v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(lean_object* v_upperBound_1225_, lean_object* v_usedInstIdxs_1226_, lean_object* v_a_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_a_1233_; uint8_t v___x_1237_; 
v___x_1237_ = lean_nat_dec_lt(v_a_1227_, v_upperBound_1225_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec(v_a_1227_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_b_1228_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1));
v___x_1240_ = l_Lean_Core_mkFreshUserName(v___x_1239_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v_fst_1242_; lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1286_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v_fst_1242_ = lean_ctor_get(v_b_1228_, 0);
v_snd_1243_ = lean_ctor_get(v_b_1228_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_b_1228_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1245_ = v_b_1228_;
v_isShared_1246_ = v_isSharedCheck_1286_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_inc(v_fst_1242_);
lean_dec(v_b_1228_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1286_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_ref_1247_; lean_object* v_quotContext_1248_; lean_object* v_currMacroScope_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_ref_1247_ = lean_ctor_get(v___y_1229_, 5);
v_quotContext_1248_ = lean_ctor_get(v___y_1229_, 10);
v_currMacroScope_1249_ = lean_ctor_get(v___y_1229_, 11);
v___x_1250_ = lean_mk_syntax_ident(v_a_1241_);
lean_inc(v___x_1250_);
v___x_1251_ = lean_array_push(v_fst_1242_, v___x_1250_);
v___x_1252_ = 0;
v___x_1253_ = l_Lean_SourceInfo_fromRef(v_ref_1247_, v___x_1252_);
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
v___x_1264_ = lean_array_push(v_snd_1243_, v___x_1263_);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_a_1227_, v_usedInstIdxs_1226_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v___x_1260_);
lean_dec(v___x_1258_);
lean_dec(v___x_1253_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1264_);
lean_ctor_set(v___x_1245_, 0, v___x_1251_);
v___x_1267_ = v___x_1245_;
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
v_a_1233_ = v___x_1267_;
goto v___jp_1232_;
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1269_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13));
v___x_1270_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14));
lean_inc_n(v___x_1253_, 4);
v___x_1271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1253_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1273_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1249_);
lean_inc(v_quotContext_1248_);
v___x_1275_ = l_Lean_addMacroScope(v_quotContext_1248_, v___x_1274_, v_currMacroScope_1249_);
v___x_1276_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1253_);
lean_ctor_set(v___x_1277_, 1, v___x_1273_);
lean_ctor_set(v___x_1277_, 2, v___x_1275_);
lean_ctor_set(v___x_1277_, 3, v___x_1276_);
v___x_1278_ = l_Lean_Syntax_node2(v___x_1253_, v___x_1272_, v___x_1277_, v___x_1258_);
v___x_1279_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22));
v___x_1280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1253_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_Syntax_node4(v___x_1253_, v___x_1269_, v___x_1271_, v___x_1260_, v___x_1278_, v___x_1280_);
v___x_1282_ = lean_array_push(v___x_1264_, v___x_1281_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1282_);
lean_ctor_set(v___x_1245_, 0, v___x_1251_);
v___x_1284_ = v___x_1245_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
v_a_1233_ = v___x_1284_;
goto v___jp_1232_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_b_1228_);
lean_dec(v_a_1227_);
v_a_1287_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1240_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1240_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
v___jp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_a_1227_, v___x_1234_);
lean_dec(v_a_1227_);
v_a_1227_ = v___x_1235_;
v_b_1228_ = v_a_1233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___boxed(lean_object* v_upperBound_1295_, lean_object* v_usedInstIdxs_1296_, lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1295_, v_usedInstIdxs_1296_, v_a_1297_, v_b_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v_usedInstIdxs_1296_);
lean_dec(v_upperBound_1295_);
return v_res_1302_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_box(1);
v___x_1304_ = l_Lean_MessageData_ofFormat(v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2));
v___x_1309_ = l_Lean_MessageData_ofFormat(v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
return v_x_1310_;
}
else
{
lean_object* v_head_1312_; lean_object* v_tail_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1335_; 
v_head_1312_ = lean_ctor_get(v_x_1311_, 0);
v_tail_1313_ = lean_ctor_get(v_x_1311_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1311_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1315_ = v_x_1311_;
v_isShared_1316_ = v_isSharedCheck_1335_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_tail_1313_);
lean_inc(v_head_1312_);
lean_dec(v_x_1311_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1335_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_before_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1333_; 
v_before_1317_ = lean_ctor_get(v_head_1312_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_head_1312_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_head_1312_, 1);
lean_dec(v_unused_1334_);
v___x_1319_ = v_head_1312_;
v_isShared_1320_ = v_isSharedCheck_1333_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_before_1317_);
lean_dec(v_head_1312_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1333_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 7);
lean_ctor_set(v___x_1319_, 1, v___x_1321_);
lean_ctor_set(v___x_1319_, 0, v_x_1310_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_x_1310_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_1316_ == 0)
{
lean_ctor_set_tag(v___x_1315_, 7);
lean_ctor_set(v___x_1315_, 1, v___x_1324_);
lean_ctor_set(v___x_1315_, 0, v___x_1323_);
v___x_1326_ = v___x_1315_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = l_Lean_MessageData_ofSyntax(v_before_1317_);
v___x_1328_ = l_Lean_indentD(v___x_1327_);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1326_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v_x_1310_ = v___x_1329_;
v_x_1311_ = v_tail_1313_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_1336_, lean_object* v_opt_1337_){
_start:
{
lean_object* v_name_1338_; lean_object* v_defValue_1339_; lean_object* v_map_1340_; lean_object* v___x_1341_; 
v_name_1338_ = lean_ctor_get(v_opt_1337_, 0);
v_defValue_1339_ = lean_ctor_get(v_opt_1337_, 1);
v_map_1340_ = lean_ctor_get(v_opts_1336_, 0);
v___x_1341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1340_, v_name_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_unbox(v_defValue_1339_);
return v___x_1342_;
}
else
{
lean_object* v_val_1343_; 
v_val_1343_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1343_);
lean_dec_ref(v___x_1341_);
if (lean_obj_tag(v_val_1343_) == 1)
{
uint8_t v_v_1344_; 
v_v_1344_ = lean_ctor_get_uint8(v_val_1343_, 0);
lean_dec_ref(v_val_1343_);
return v_v_1344_;
}
else
{
uint8_t v___x_1345_; 
lean_dec(v_val_1343_);
v___x_1345_ = lean_unbox(v_defValue_1339_);
return v___x_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_1346_, lean_object* v_opt_1347_){
_start:
{
uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_res_1348_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_1346_, v_opt_1347_);
lean_dec_ref(v_opt_1347_);
lean_dec_ref(v_opts_1346_);
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1354_ = l_Lean_MessageData_ofFormat(v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_1355_, lean_object* v_macroStack_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_options_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_options_1359_ = lean_ctor_get(v___y_1357_, 2);
v___x_1360_ = l_Lean_Elab_pp_macroStack;
v___x_1361_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec(v_macroStack_1356_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_msgData_1355_);
return v___x_1362_;
}
else
{
if (lean_obj_tag(v_macroStack_1356_) == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_msgData_1355_);
return v___x_1363_;
}
else
{
lean_object* v_head_1364_; lean_object* v_after_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1380_; 
v_head_1364_ = lean_ctor_get(v_macroStack_1356_, 0);
lean_inc(v_head_1364_);
v_after_1365_ = lean_ctor_get(v_head_1364_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_head_1364_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v_head_1364_, 0);
lean_dec(v_unused_1381_);
v___x_1367_ = v_head_1364_;
v_isShared_1368_ = v_isSharedCheck_1380_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_after_1365_);
lean_dec(v_head_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1380_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 7);
lean_ctor_set(v___x_1367_, 1, v___x_1369_);
lean_ctor_set(v___x_1367_, 0, v_msgData_1355_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_msgData_1355_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_msgData_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1372_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_MessageData_ofSyntax(v_after_1365_);
v___x_1375_ = l_Lean_indentD(v___x_1374_);
v_msgData_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1376_, 0, v___x_1373_);
lean_ctor_set(v_msgData_1376_, 1, v___x_1375_);
v___x_1377_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_1376_, v_macroStack_1356_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1382_, lean_object* v_macroStack_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1382_, v_macroStack_1383_, v___y_1384_);
lean_dec_ref(v___y_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(lean_object* v_msg_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_ref_1395_; lean_object* v___x_1396_; lean_object* v_a_1397_; lean_object* v_macroStack_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
v_ref_1395_ = lean_ctor_get(v___y_1392_, 5);
v___x_1396_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1387_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___x_1396_);
v_macroStack_1398_ = lean_ctor_get(v___y_1388_, 1);
v___x_1399_ = l_Lean_Elab_getBetterRef(v_ref_1395_, v_macroStack_1398_);
lean_inc(v_macroStack_1398_);
v___x_1400_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_a_1397_, v_macroStack_1398_, v___y_1392_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1399_);
lean_ctor_set(v___x_1405_, 1, v_a_1401_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 1);
lean_ctor_set(v___x_1403_, 0, v___x_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1418_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0));
v___x_1421_ = l_Lean_stringToMessageData(v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2));
v___x_1424_ = l_Lean_stringToMessageData(v___x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(lean_object* v_constName_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v_env_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_st_ref_get(v___y_1431_);
v_env_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc_ref(v_env_1434_);
lean_dec(v___x_1433_);
lean_inc(v_constName_1425_);
v___x_1435_ = l_Lean_isInductiveCore_x3f(v_env_1434_, v_constName_1425_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1436_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_1437_ = 0;
v___x_1438_ = l_Lean_MessageData_ofConstName(v_constName_1425_, v___x_1437_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1436_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_1441_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1442_;
}
else
{
lean_object* v_val_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_constName_1425_);
v_val_1443_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1435_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_val_1443_);
lean_dec(v___x_1435_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 0);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_val_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___boxed(lean_object* v_constName_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_constName_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(size_t v_sz_1460_, size_t v_i_1461_, lean_object* v_bs_1462_){
_start:
{
uint8_t v___x_1463_; 
v___x_1463_ = lean_usize_dec_lt(v_i_1461_, v_sz_1460_);
if (v___x_1463_ == 0)
{
return v_bs_1462_;
}
else
{
lean_object* v_v_1464_; lean_object* v___x_1465_; lean_object* v_bs_x27_1466_; size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v_v_1464_ = lean_array_uget(v_bs_1462_, v_i_1461_);
v___x_1465_ = lean_unsigned_to_nat(0u);
v_bs_x27_1466_ = lean_array_uset(v_bs_1462_, v_i_1461_, v___x_1465_);
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_add(v_i_1461_, v___x_1467_);
v___x_1469_ = lean_array_uset(v_bs_x27_1466_, v_i_1461_, v_v_1464_);
v_i_1461_ = v___x_1468_;
v_bs_1462_ = v___x_1469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0___boxed(lean_object* v_sz_1471_, lean_object* v_i_1472_, lean_object* v_bs_1473_){
_start:
{
size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1471_);
lean_dec(v_sz_1471_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_boxed_1474_, v_i_boxed_1475_, v_bs_1473_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(lean_object* v_inductiveTypeName_1554_, lean_object* v_instId_1555_, lean_object* v_usedInstIdxs_1556_, lean_object* v_auxFunId_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; 
lean_inc(v_inductiveTypeName_1554_);
v___x_1565_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_1554_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_numParams_1567_; lean_object* v_numIndices_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1565_);
v_numParams_1567_ = lean_ctor_get(v_a_1566_, 1);
lean_inc(v_numParams_1567_);
v_numIndices_1568_ = lean_ctor_get(v_a_1566_, 2);
lean_inc(v_numIndices_1568_);
lean_dec(v_a_1566_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_nat_add(v_numParams_1567_, v_numIndices_1568_);
lean_dec(v_numIndices_1568_);
lean_dec(v_numParams_1567_);
v___x_1571_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1));
v___x_1572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v___x_1570_, v_usedInstIdxs_1556_, v___x_1569_, v___x_1571_, v_a_1562_, v_a_1563_);
lean_dec(v___x_1570_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1649_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1649_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1649_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_fst_1577_; lean_object* v_snd_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1648_; 
v_fst_1577_ = lean_ctor_get(v_a_1573_, 0);
v_snd_1578_ = lean_ctor_get(v_a_1573_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_a_1573_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1580_ = v_a_1573_;
v_isShared_1581_ = v_isSharedCheck_1648_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snd_1578_);
lean_inc(v_fst_1577_);
lean_dec(v_a_1573_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1648_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_ref_1582_; lean_object* v_quotContext_1583_; lean_object* v_currMacroScope_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v_ref_1582_ = lean_ctor_get(v_a_1562_, 5);
v_quotContext_1583_ = lean_ctor_get(v_a_1562_, 10);
v_currMacroScope_1584_ = lean_ctor_get(v_a_1562_, 11);
v___x_1585_ = 0;
v___x_1586_ = l_Lean_SourceInfo_fromRef(v_ref_1582_, v___x_1585_);
v___x_1587_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1588_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3));
v___x_1589_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4));
lean_inc(v___x_1586_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 2);
lean_ctor_set(v___x_1580_, 1, v___x_1589_);
lean_ctor_set(v___x_1580_, 0, v___x_1586_);
v___x_1591_ = v___x_1580_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; size_t v_sz_1612_; size_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1592_ = l_Lean_mkCIdent(v_inductiveTypeName_1554_);
lean_inc_n(v___x_1586_, 24);
v___x_1593_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1588_, v___x_1591_, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1595_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1596_ = l_Array_append___redArg(v___x_1595_, v_fst_1577_);
lean_dec(v_fst_1577_);
v___x_1597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1586_);
lean_ctor_set(v___x_1597_, 1, v___x_1594_);
lean_ctor_set(v___x_1597_, 2, v___x_1596_);
v___x_1598_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1587_, v___x_1593_, v___x_1597_);
v___x_1599_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7));
v___x_1600_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9));
v___x_1601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1586_);
lean_ctor_set(v___x_1601_, 1, v___x_1594_);
lean_ctor_set(v___x_1601_, 2, v___x_1595_);
lean_inc_ref_n(v___x_1601_, 12);
v___x_1602_ = l_Lean_Syntax_node7(v___x_1586_, v___x_1600_, v___x_1601_, v___x_1601_, v___x_1601_, v___x_1601_, v___x_1601_, v___x_1601_, v___x_1601_);
v___x_1603_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10));
v___x_1604_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11));
v___x_1605_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13));
v___x_1606_ = l_Lean_Syntax_node1(v___x_1586_, v___x_1605_, v___x_1601_);
v___x_1607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1586_);
lean_ctor_set(v___x_1607_, 1, v___x_1603_);
v___x_1608_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15));
v___x_1609_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1608_, v_instId_1555_, v___x_1601_);
v___x_1610_ = l_Lean_Syntax_node1(v___x_1586_, v___x_1594_, v___x_1609_);
v___x_1611_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17));
v_sz_1612_ = lean_array_size(v_snd_1578_);
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_1612_, v___x_1613_, v_snd_1578_);
v___x_1615_ = l_Array_append___redArg(v___x_1595_, v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1586_);
lean_ctor_set(v___x_1616_, 1, v___x_1594_);
lean_ctor_set(v___x_1616_, 2, v___x_1615_);
v___x_1617_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19));
v___x_1618_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20));
v___x_1619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1586_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1621_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1584_);
lean_inc(v_quotContext_1583_);
v___x_1622_ = l_Lean_addMacroScope(v_quotContext_1583_, v___x_1621_, v_currMacroScope_1584_);
v___x_1623_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1624_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1586_);
lean_ctor_set(v___x_1624_, 1, v___x_1620_);
lean_ctor_set(v___x_1624_, 2, v___x_1622_);
lean_ctor_set(v___x_1624_, 3, v___x_1623_);
v___x_1625_ = l_Lean_Syntax_node1(v___x_1586_, v___x_1594_, v___x_1598_);
v___x_1626_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1587_, v___x_1624_, v___x_1625_);
v___x_1627_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1617_, v___x_1619_, v___x_1626_);
v___x_1628_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1611_, v___x_1616_, v___x_1627_);
v___x_1629_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22));
v___x_1630_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23));
v___x_1631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1586_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25));
v___x_1633_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1586_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_Syntax_node1(v___x_1586_, v___x_1594_, v_auxFunId_1557_);
v___x_1636_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27));
v___x_1637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1586_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = l_Lean_Syntax_node3(v___x_1586_, v___x_1632_, v___x_1634_, v___x_1635_, v___x_1637_);
v___x_1639_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30));
v___x_1640_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1639_, v___x_1601_, v___x_1601_);
v___x_1641_ = l_Lean_Syntax_node4(v___x_1586_, v___x_1629_, v___x_1631_, v___x_1638_, v___x_1640_, v___x_1601_);
v___x_1642_ = l_Lean_Syntax_node6(v___x_1586_, v___x_1604_, v___x_1606_, v___x_1607_, v___x_1601_, v___x_1610_, v___x_1628_, v___x_1641_);
v___x_1643_ = l_Lean_Syntax_node2(v___x_1586_, v___x_1599_, v___x_1602_, v___x_1642_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1643_);
v___x_1645_ = v___x_1575_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_auxFunId_1557_);
lean_dec(v_instId_1555_);
lean_dec(v_inductiveTypeName_1554_);
v_a_1650_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1572_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1572_);
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
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_auxFunId_1557_);
lean_dec(v_instId_1555_);
lean_dec(v_inductiveTypeName_1554_);
v_a_1658_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1565_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1565_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___boxed(lean_object* v_inductiveTypeName_1666_, lean_object* v_instId_1667_, lean_object* v_usedInstIdxs_1668_, lean_object* v_auxFunId_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_1666_, v_instId_1667_, v_usedInstIdxs_1668_, v_auxFunId_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_usedInstIdxs_1668_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(lean_object* v_upperBound_1678_, lean_object* v_usedInstIdxs_1679_, lean_object* v_inst_1680_, lean_object* v_R_1681_, lean_object* v_a_1682_, lean_object* v_b_1683_, lean_object* v_c_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1678_, v_usedInstIdxs_1679_, v_a_1682_, v_b_1683_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___boxed(lean_object* v_upperBound_1693_, lean_object* v_usedInstIdxs_1694_, lean_object* v_inst_1695_, lean_object* v_R_1696_, lean_object* v_a_1697_, lean_object* v_b_1698_, lean_object* v_c_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(v_upperBound_1693_, v_usedInstIdxs_1694_, v_inst_1695_, v_R_1696_, v_a_1697_, v_b_1698_, v_c_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v_usedInstIdxs_1694_);
lean_dec(v_upperBound_1693_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_object* v_00_u03b1_1708_, lean_object* v_msg_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_msg_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(v_00_u03b1_1718_, v_msg_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(lean_object* v_msgData_1728_, lean_object* v_macroStack_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1728_, v_macroStack_1729_, v___y_1734_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1738_, lean_object* v_macroStack_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(v_msgData_1738_, v_macroStack_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1747_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = lean_unsigned_to_nat(32u);
v___x_1749_ = lean_mk_empty_array_with_capacity(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = ((size_t)5ULL);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_unsigned_to_nat(32u);
v___x_1754_ = lean_mk_empty_array_with_capacity(v___x_1753_);
v___x_1755_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0);
v___x_1756_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1754_);
lean_ctor_set(v___x_1756_, 2, v___x_1752_);
lean_ctor_set(v___x_1756_, 3, v___x_1752_);
lean_ctor_set_usize(v___x_1756_, 4, v___x_1751_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v_traceState_1760_; lean_object* v_traces_1761_; lean_object* v___x_1762_; lean_object* v_traceState_1763_; lean_object* v_env_1764_; lean_object* v_nextMacroScope_1765_; lean_object* v_ngen_1766_; lean_object* v_auxDeclNGen_1767_; lean_object* v_cache_1768_; lean_object* v_messages_1769_; lean_object* v_infoState_1770_; lean_object* v_snapshotTasks_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1790_; 
v___x_1759_ = lean_st_ref_get(v___y_1757_);
v_traceState_1760_ = lean_ctor_get(v___x_1759_, 4);
lean_inc_ref(v_traceState_1760_);
lean_dec(v___x_1759_);
v_traces_1761_ = lean_ctor_get(v_traceState_1760_, 0);
lean_inc_ref(v_traces_1761_);
lean_dec_ref(v_traceState_1760_);
v___x_1762_ = lean_st_ref_take(v___y_1757_);
v_traceState_1763_ = lean_ctor_get(v___x_1762_, 4);
v_env_1764_ = lean_ctor_get(v___x_1762_, 0);
v_nextMacroScope_1765_ = lean_ctor_get(v___x_1762_, 1);
v_ngen_1766_ = lean_ctor_get(v___x_1762_, 2);
v_auxDeclNGen_1767_ = lean_ctor_get(v___x_1762_, 3);
v_cache_1768_ = lean_ctor_get(v___x_1762_, 5);
v_messages_1769_ = lean_ctor_get(v___x_1762_, 6);
v_infoState_1770_ = lean_ctor_get(v___x_1762_, 7);
v_snapshotTasks_1771_ = lean_ctor_get(v___x_1762_, 8);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1773_ = v___x_1762_;
v_isShared_1774_ = v_isSharedCheck_1790_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snapshotTasks_1771_);
lean_inc(v_infoState_1770_);
lean_inc(v_messages_1769_);
lean_inc(v_cache_1768_);
lean_inc(v_traceState_1763_);
lean_inc(v_auxDeclNGen_1767_);
lean_inc(v_ngen_1766_);
lean_inc(v_nextMacroScope_1765_);
lean_inc(v_env_1764_);
lean_dec(v___x_1762_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1790_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
uint64_t v_tid_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1788_; 
v_tid_1775_ = lean_ctor_get_uint64(v_traceState_1763_, sizeof(void*)*1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_traceState_1763_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v_traceState_1763_, 0);
lean_dec(v_unused_1789_);
v___x_1777_ = v_traceState_1763_;
v_isShared_1778_ = v_isSharedCheck_1788_;
goto v_resetjp_1776_;
}
else
{
lean_dec(v_traceState_1763_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1788_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1779_);
lean_ctor_set_uint64(v_reuseFailAlloc_1787_, sizeof(void*)*1, v_tid_1775_);
v___x_1781_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 4, v___x_1781_);
v___x_1783_ = v___x_1773_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_env_1764_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_nextMacroScope_1765_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_ngen_1766_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_auxDeclNGen_1767_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1786_, 5, v_cache_1768_);
lean_ctor_set(v_reuseFailAlloc_1786_, 6, v_messages_1769_);
lean_ctor_set(v_reuseFailAlloc_1786_, 7, v_infoState_1770_);
lean_ctor_set(v_reuseFailAlloc_1786_, 8, v_snapshotTasks_1771_);
v___x_1783_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_st_ref_set(v___y_1757_, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_traces_1761_);
return v___x_1785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___boxed(lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1791_);
lean_dec(v___y_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
v___x_1818_ = lean_apply_7(v_x_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, lean_box(0));
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object* v_mvarId_1828_, lean_object* v_x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___f_1837_; lean_object* v___x_1838_; 
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1837_, 0, v_x_1829_);
lean_closure_set(v___f_1837_, 1, v___y_1830_);
lean_closure_set(v___f_1837_, 2, v___y_1831_);
v___x_1838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1828_, v___f_1837_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1838_) == 0)
{
return v___x_1838_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object* v_mvarId_1847_, lean_object* v_x_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1847_, v_x_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object* v_00_u03b1_1857_, lean_object* v_mvarId_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1858_, v_x_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_mvarId_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(v_00_u03b1_1868_, v_mvarId_1869_, v_x_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1878_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0));
v___x_1881_ = l_Lean_stringToMessageData(v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object* v_a_1882_, lean_object* v_x_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1891_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1);
v___x_1892_ = lean_unsigned_to_nat(30u);
v___x_1893_ = l_Lean_inlineExprTrailing(v_a_1882_, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1891_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object* v_a_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(v_a_1896_, v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec_ref(v_x_1897_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6_spec__10(size_t v_sz_1906_, size_t v_i_1907_, lean_object* v_bs_1908_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_usize_dec_lt(v_i_1907_, v_sz_1906_);
if (v___x_1909_ == 0)
{
return v_bs_1908_;
}
else
{
lean_object* v_v_1910_; lean_object* v_msg_1911_; lean_object* v___x_1912_; lean_object* v_bs_x27_1913_; size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v_v_1910_ = lean_array_uget_borrowed(v_bs_1908_, v_i_1907_);
v_msg_1911_ = lean_ctor_get(v_v_1910_, 1);
lean_inc_ref(v_msg_1911_);
v___x_1912_ = lean_unsigned_to_nat(0u);
v_bs_x27_1913_ = lean_array_uset(v_bs_1908_, v_i_1907_, v___x_1912_);
v___x_1914_ = ((size_t)1ULL);
v___x_1915_ = lean_usize_add(v_i_1907_, v___x_1914_);
v___x_1916_ = lean_array_uset(v_bs_x27_1913_, v_i_1907_, v_msg_1911_);
v_i_1907_ = v___x_1915_;
v_bs_1908_ = v___x_1916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6_spec__10___boxed(lean_object* v_sz_1918_, lean_object* v_i_1919_, lean_object* v_bs_1920_){
_start:
{
size_t v_sz_boxed_1921_; size_t v_i_boxed_1922_; lean_object* v_res_1923_; 
v_sz_boxed_1921_ = lean_unbox_usize(v_sz_1918_);
lean_dec(v_sz_1918_);
v_i_boxed_1922_ = lean_unbox_usize(v_i_1919_);
lean_dec(v_i_1919_);
v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6_spec__10(v_sz_boxed_1921_, v_i_boxed_1922_, v_bs_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object* v_oldTraces_1924_, lean_object* v_data_1925_, lean_object* v_ref_1926_, lean_object* v_msg_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_fileName_1933_; lean_object* v_fileMap_1934_; lean_object* v_options_1935_; lean_object* v_currRecDepth_1936_; lean_object* v_maxRecDepth_1937_; lean_object* v_ref_1938_; lean_object* v_currNamespace_1939_; lean_object* v_openDecls_1940_; lean_object* v_initHeartbeats_1941_; lean_object* v_maxHeartbeats_1942_; lean_object* v_quotContext_1943_; lean_object* v_currMacroScope_1944_; uint8_t v_diag_1945_; lean_object* v_cancelTk_x3f_1946_; uint8_t v_suppressElabErrors_1947_; lean_object* v_inheritedTraceOptions_1948_; lean_object* v___x_1949_; lean_object* v_traceState_1950_; lean_object* v_traces_1951_; lean_object* v_ref_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; size_t v_sz_1955_; size_t v___x_1956_; lean_object* v___x_1957_; lean_object* v_msg_1958_; lean_object* v___x_1959_; lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1997_; 
v_fileName_1933_ = lean_ctor_get(v___y_1930_, 0);
v_fileMap_1934_ = lean_ctor_get(v___y_1930_, 1);
v_options_1935_ = lean_ctor_get(v___y_1930_, 2);
v_currRecDepth_1936_ = lean_ctor_get(v___y_1930_, 3);
v_maxRecDepth_1937_ = lean_ctor_get(v___y_1930_, 4);
v_ref_1938_ = lean_ctor_get(v___y_1930_, 5);
v_currNamespace_1939_ = lean_ctor_get(v___y_1930_, 6);
v_openDecls_1940_ = lean_ctor_get(v___y_1930_, 7);
v_initHeartbeats_1941_ = lean_ctor_get(v___y_1930_, 8);
v_maxHeartbeats_1942_ = lean_ctor_get(v___y_1930_, 9);
v_quotContext_1943_ = lean_ctor_get(v___y_1930_, 10);
v_currMacroScope_1944_ = lean_ctor_get(v___y_1930_, 11);
v_diag_1945_ = lean_ctor_get_uint8(v___y_1930_, sizeof(void*)*14);
v_cancelTk_x3f_1946_ = lean_ctor_get(v___y_1930_, 12);
v_suppressElabErrors_1947_ = lean_ctor_get_uint8(v___y_1930_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1948_ = lean_ctor_get(v___y_1930_, 13);
v___x_1949_ = lean_st_ref_get(v___y_1931_);
v_traceState_1950_ = lean_ctor_get(v___x_1949_, 4);
lean_inc_ref(v_traceState_1950_);
lean_dec(v___x_1949_);
v_traces_1951_ = lean_ctor_get(v_traceState_1950_, 0);
lean_inc_ref(v_traces_1951_);
lean_dec_ref(v_traceState_1950_);
v_ref_1952_ = l_Lean_replaceRef(v_ref_1926_, v_ref_1938_);
lean_inc_ref(v_inheritedTraceOptions_1948_);
lean_inc(v_cancelTk_x3f_1946_);
lean_inc(v_currMacroScope_1944_);
lean_inc(v_quotContext_1943_);
lean_inc(v_maxHeartbeats_1942_);
lean_inc(v_initHeartbeats_1941_);
lean_inc(v_openDecls_1940_);
lean_inc(v_currNamespace_1939_);
lean_inc(v_maxRecDepth_1937_);
lean_inc(v_currRecDepth_1936_);
lean_inc_ref(v_options_1935_);
lean_inc_ref(v_fileMap_1934_);
lean_inc_ref(v_fileName_1933_);
v___x_1953_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1953_, 0, v_fileName_1933_);
lean_ctor_set(v___x_1953_, 1, v_fileMap_1934_);
lean_ctor_set(v___x_1953_, 2, v_options_1935_);
lean_ctor_set(v___x_1953_, 3, v_currRecDepth_1936_);
lean_ctor_set(v___x_1953_, 4, v_maxRecDepth_1937_);
lean_ctor_set(v___x_1953_, 5, v_ref_1952_);
lean_ctor_set(v___x_1953_, 6, v_currNamespace_1939_);
lean_ctor_set(v___x_1953_, 7, v_openDecls_1940_);
lean_ctor_set(v___x_1953_, 8, v_initHeartbeats_1941_);
lean_ctor_set(v___x_1953_, 9, v_maxHeartbeats_1942_);
lean_ctor_set(v___x_1953_, 10, v_quotContext_1943_);
lean_ctor_set(v___x_1953_, 11, v_currMacroScope_1944_);
lean_ctor_set(v___x_1953_, 12, v_cancelTk_x3f_1946_);
lean_ctor_set(v___x_1953_, 13, v_inheritedTraceOptions_1948_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*14, v_diag_1945_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*14 + 1, v_suppressElabErrors_1947_);
v___x_1954_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1951_);
lean_dec_ref(v_traces_1951_);
v_sz_1955_ = lean_array_size(v___x_1954_);
v___x_1956_ = ((size_t)0ULL);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6_spec__10(v_sz_1955_, v___x_1956_, v___x_1954_);
v_msg_1958_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1958_, 0, v_data_1925_);
lean_ctor_set(v_msg_1958_, 1, v_msg_1927_);
lean_ctor_set(v_msg_1958_, 2, v___x_1957_);
v___x_1959_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1958_, v___y_1928_, v___y_1929_, v___x_1953_, v___y_1931_);
lean_dec_ref(v___x_1953_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1997_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1997_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v_traceState_1965_; lean_object* v_env_1966_; lean_object* v_nextMacroScope_1967_; lean_object* v_ngen_1968_; lean_object* v_auxDeclNGen_1969_; lean_object* v_cache_1970_; lean_object* v_messages_1971_; lean_object* v_infoState_1972_; lean_object* v_snapshotTasks_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1996_; 
v___x_1964_ = lean_st_ref_take(v___y_1931_);
v_traceState_1965_ = lean_ctor_get(v___x_1964_, 4);
v_env_1966_ = lean_ctor_get(v___x_1964_, 0);
v_nextMacroScope_1967_ = lean_ctor_get(v___x_1964_, 1);
v_ngen_1968_ = lean_ctor_get(v___x_1964_, 2);
v_auxDeclNGen_1969_ = lean_ctor_get(v___x_1964_, 3);
v_cache_1970_ = lean_ctor_get(v___x_1964_, 5);
v_messages_1971_ = lean_ctor_get(v___x_1964_, 6);
v_infoState_1972_ = lean_ctor_get(v___x_1964_, 7);
v_snapshotTasks_1973_ = lean_ctor_get(v___x_1964_, 8);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1975_ = v___x_1964_;
v_isShared_1976_ = v_isSharedCheck_1996_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_snapshotTasks_1973_);
lean_inc(v_infoState_1972_);
lean_inc(v_messages_1971_);
lean_inc(v_cache_1970_);
lean_inc(v_traceState_1965_);
lean_inc(v_auxDeclNGen_1969_);
lean_inc(v_ngen_1968_);
lean_inc(v_nextMacroScope_1967_);
lean_inc(v_env_1966_);
lean_dec(v___x_1964_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1996_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
uint64_t v_tid_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1994_; 
v_tid_1977_ = lean_ctor_get_uint64(v_traceState_1965_, sizeof(void*)*1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_traceState_1965_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v_traceState_1965_, 0);
lean_dec(v_unused_1995_);
v___x_1979_ = v_traceState_1965_;
v_isShared_1980_ = v_isSharedCheck_1994_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_traceState_1965_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1994_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_ref_1926_);
lean_ctor_set(v___x_1981_, 1, v_a_1960_);
v___x_1982_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1924_, v___x_1981_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1982_);
v___x_1984_ = v___x_1979_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1982_);
lean_ctor_set_uint64(v_reuseFailAlloc_1993_, sizeof(void*)*1, v_tid_1977_);
v___x_1984_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v___x_1984_);
v___x_1986_ = v___x_1975_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_env_1966_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_nextMacroScope_1967_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_ngen_1968_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v_auxDeclNGen_1969_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1992_, 5, v_cache_1970_);
lean_ctor_set(v_reuseFailAlloc_1992_, 6, v_messages_1971_);
lean_ctor_set(v_reuseFailAlloc_1992_, 7, v_infoState_1972_);
lean_ctor_set(v_reuseFailAlloc_1992_, 8, v_snapshotTasks_1973_);
v___x_1986_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1987_ = lean_st_ref_set(v___y_1931_, v___x_1986_);
v___x_1988_ = lean_box(0);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1988_);
v___x_1990_ = v___x_1962_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg___boxed(lean_object* v_oldTraces_1998_, lean_object* v_data_1999_, lean_object* v_ref_2000_, lean_object* v_msg_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_oldTraces_1998_, v_data_1999_, v_ref_2000_, v_msg_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2007_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object* v_e_2008_){
_start:
{
if (lean_obj_tag(v_e_2008_) == 0)
{
uint8_t v___x_2009_; 
v___x_2009_ = 2;
return v___x_2009_;
}
else
{
uint8_t v___x_2010_; 
v___x_2010_ = 0;
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object* v_e_2011_){
_start:
{
uint8_t v_res_2012_; lean_object* v_r_2013_; 
v_res_2012_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_e_2011_);
lean_dec_ref(v_e_2011_);
v_r_2013_ = lean_box(v_res_2012_);
return v_r_2013_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(lean_object* v_x_2014_){
_start:
{
if (lean_obj_tag(v_x_2014_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_a_2016_ = lean_ctor_get(v_x_2014_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_x_2014_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v_x_2014_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v_x_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 1);
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_a_2024_ = lean_ctor_get(v_x_2014_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_x_2014_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v_x_2014_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v_x_2014_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 0);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg___boxed(lean_object* v_x_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(v_x_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object* v_opts_2035_, lean_object* v_opt_2036_){
_start:
{
lean_object* v_name_2037_; lean_object* v_defValue_2038_; lean_object* v_map_2039_; lean_object* v___x_2040_; 
v_name_2037_ = lean_ctor_get(v_opt_2036_, 0);
v_defValue_2038_ = lean_ctor_get(v_opt_2036_, 1);
v_map_2039_ = lean_ctor_get(v_opts_2035_, 0);
v___x_2040_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2039_, v_name_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_inc(v_defValue_2038_);
return v_defValue_2038_;
}
else
{
lean_object* v_val_2041_; 
v_val_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_val_2041_);
lean_dec_ref(v___x_2040_);
if (lean_obj_tag(v_val_2041_) == 3)
{
lean_object* v_v_2042_; 
v_v_2042_ = lean_ctor_get(v_val_2041_, 0);
lean_inc(v_v_2042_);
lean_dec_ref(v_val_2041_);
return v_v_2042_;
}
else
{
lean_dec(v_val_2041_);
lean_inc(v_defValue_2038_);
return v_defValue_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___boxed(lean_object* v_opts_2043_, lean_object* v_opt_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2043_, v_opt_2044_);
lean_dec_ref(v_opt_2044_);
lean_dec_ref(v_opts_2043_);
return v_res_2045_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2));
v___x_2051_ = l_Lean_stringToMessageData(v___x_2050_);
return v___x_2051_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2052_; double v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(1000u);
v___x_2053_ = lean_float_of_nat(v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object* v_cls_2054_, uint8_t v_collapsed_2055_, lean_object* v_tag_2056_, lean_object* v_opts_2057_, uint8_t v_clsEnabled_2058_, lean_object* v_oldTraces_2059_, lean_object* v_msg_2060_, lean_object* v_resStartStop_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2160_; 
v_fst_2069_ = lean_ctor_get(v_resStartStop_2061_, 0);
v_snd_2070_ = lean_ctor_get(v_resStartStop_2061_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_resStartStop_2061_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2072_ = v_resStartStop_2061_;
v_isShared_2073_ = v_isSharedCheck_2160_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snd_2070_);
lean_inc(v_fst_2069_);
lean_dec(v_resStartStop_2061_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2160_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v_data_2077_; lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2159_; 
v_fst_2080_ = lean_ctor_get(v_snd_2070_, 0);
v_snd_2081_ = lean_ctor_get(v_snd_2070_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_snd_2070_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2083_ = v_snd_2070_;
v_isShared_2084_ = v_isSharedCheck_2159_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_snd_2081_);
lean_inc(v_fst_2080_);
lean_dec(v_snd_2070_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2159_;
goto v_resetjp_2082_;
}
v___jp_2074_:
{
lean_object* v___x_2078_; 
lean_inc(v___y_2075_);
v___x_2078_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_oldTraces_2059_, v_data_2077_, v___y_2075_, v___y_2076_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; 
lean_dec_ref(v___x_2078_);
v___x_2079_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(v_fst_2069_);
return v___x_2079_;
}
else
{
lean_dec(v_fst_2069_);
return v___x_2078_;
}
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___y_2088_; lean_object* v_a_2089_; uint8_t v___y_2113_; double v___y_2144_; 
v___x_2085_ = l_Lean_trace_profiler;
v___x_2086_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2057_, v___x_2085_);
if (v___x_2086_ == 0)
{
v___y_2113_ = v___x_2086_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2150_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2057_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; double v___x_2153_; double v___x_2154_; double v___x_2155_; 
v___x_2151_ = l_Lean_trace_profiler_threshold;
v___x_2152_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2057_, v___x_2151_);
v___x_2153_ = lean_float_of_nat(v___x_2152_);
v___x_2154_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4);
v___x_2155_ = lean_float_div(v___x_2153_, v___x_2154_);
v___y_2144_ = v___x_2155_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; double v___x_2158_; 
v___x_2156_ = l_Lean_trace_profiler_threshold;
v___x_2157_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2057_, v___x_2156_);
v___x_2158_ = lean_float_of_nat(v___x_2157_);
v___y_2144_ = v___x_2158_;
goto v___jp_2143_;
}
}
v___jp_2087_:
{
uint8_t v_result_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v_result_2090_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_fst_2069_);
v___x_2091_ = l_Lean_TraceResult_toEmoji(v_result_2090_);
v___x_2092_ = l_Lean_stringToMessageData(v___x_2091_);
v___x_2093_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 7);
lean_ctor_set(v___x_2083_, 1, v___x_2093_);
lean_ctor_set(v___x_2083_, 0, v___x_2092_);
v___x_2095_ = v___x_2083_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v_m_2097_; 
if (v_isShared_2073_ == 0)
{
lean_ctor_set_tag(v___x_2072_, 7);
lean_ctor_set(v___x_2072_, 1, v_a_2089_);
lean_ctor_set(v___x_2072_, 0, v___x_2095_);
v_m_2097_ = v___x_2072_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_a_2089_);
v_m_2097_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; double v___x_2100_; lean_object* v_data_2101_; 
v___x_2098_ = lean_box(v_result_2090_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
v___x_2100_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2056_);
lean_inc_ref(v___x_2099_);
lean_inc(v_cls_2054_);
v_data_2101_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2101_, 0, v_cls_2054_);
lean_ctor_set(v_data_2101_, 1, v___x_2099_);
lean_ctor_set(v_data_2101_, 2, v_tag_2056_);
lean_ctor_set_float(v_data_2101_, sizeof(void*)*3, v___x_2100_);
lean_ctor_set_float(v_data_2101_, sizeof(void*)*3 + 8, v___x_2100_);
lean_ctor_set_uint8(v_data_2101_, sizeof(void*)*3 + 16, v_collapsed_2055_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v___x_2099_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2080_);
lean_dec_ref(v_tag_2056_);
lean_dec(v_cls_2054_);
v___y_2075_ = v___y_2088_;
v___y_2076_ = v_m_2097_;
v_data_2077_ = v_data_2101_;
goto v___jp_2074_;
}
else
{
lean_object* v_data_2102_; double v___x_2103_; double v___x_2104_; 
lean_dec_ref(v_data_2101_);
v_data_2102_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2102_, 0, v_cls_2054_);
lean_ctor_set(v_data_2102_, 1, v___x_2099_);
lean_ctor_set(v_data_2102_, 2, v_tag_2056_);
v___x_2103_ = lean_unbox_float(v_fst_2080_);
lean_dec(v_fst_2080_);
lean_ctor_set_float(v_data_2102_, sizeof(void*)*3, v___x_2103_);
v___x_2104_ = lean_unbox_float(v_snd_2081_);
lean_dec(v_snd_2081_);
lean_ctor_set_float(v_data_2102_, sizeof(void*)*3 + 8, v___x_2104_);
lean_ctor_set_uint8(v_data_2102_, sizeof(void*)*3 + 16, v_collapsed_2055_);
v___y_2075_ = v___y_2088_;
v___y_2076_ = v_m_2097_;
v_data_2077_ = v_data_2102_;
goto v___jp_2074_;
}
}
}
}
v___jp_2107_:
{
lean_object* v_ref_2108_; lean_object* v___x_2109_; 
v_ref_2108_ = lean_ctor_get(v___y_2066_, 5);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2066_);
lean_inc(v___y_2065_);
lean_inc_ref(v___y_2064_);
lean_inc(v___y_2063_);
lean_inc_ref(v___y_2062_);
lean_inc(v_fst_2069_);
v___x_2109_ = lean_apply_8(v_msg_2060_, v_fst_2069_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, lean_box(0));
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v___y_2088_ = v_ref_2108_;
v_a_2089_ = v_a_2110_;
goto v___jp_2087_;
}
else
{
lean_object* v___x_2111_; 
lean_dec_ref(v___x_2109_);
v___x_2111_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3);
v___y_2088_ = v_ref_2108_;
v_a_2089_ = v___x_2111_;
goto v___jp_2087_;
}
}
v___jp_2112_:
{
if (v_clsEnabled_2058_ == 0)
{
if (v___y_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v_traceState_2115_; lean_object* v_env_2116_; lean_object* v_nextMacroScope_2117_; lean_object* v_ngen_2118_; lean_object* v_auxDeclNGen_2119_; lean_object* v_cache_2120_; lean_object* v_messages_2121_; lean_object* v_infoState_2122_; lean_object* v_snapshotTasks_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_2083_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2080_);
lean_del_object(v___x_2072_);
lean_dec_ref(v_msg_2060_);
lean_dec_ref(v_tag_2056_);
lean_dec(v_cls_2054_);
v___x_2114_ = lean_st_ref_take(v___y_2067_);
v_traceState_2115_ = lean_ctor_get(v___x_2114_, 4);
v_env_2116_ = lean_ctor_get(v___x_2114_, 0);
v_nextMacroScope_2117_ = lean_ctor_get(v___x_2114_, 1);
v_ngen_2118_ = lean_ctor_get(v___x_2114_, 2);
v_auxDeclNGen_2119_ = lean_ctor_get(v___x_2114_, 3);
v_cache_2120_ = lean_ctor_get(v___x_2114_, 5);
v_messages_2121_ = lean_ctor_get(v___x_2114_, 6);
v_infoState_2122_ = lean_ctor_get(v___x_2114_, 7);
v_snapshotTasks_2123_ = lean_ctor_get(v___x_2114_, 8);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2125_ = v___x_2114_;
v_isShared_2126_ = v_isSharedCheck_2142_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_snapshotTasks_2123_);
lean_inc(v_infoState_2122_);
lean_inc(v_messages_2121_);
lean_inc(v_cache_2120_);
lean_inc(v_traceState_2115_);
lean_inc(v_auxDeclNGen_2119_);
lean_inc(v_ngen_2118_);
lean_inc(v_nextMacroScope_2117_);
lean_inc(v_env_2116_);
lean_dec(v___x_2114_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2142_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
uint64_t v_tid_2127_; lean_object* v_traces_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2141_; 
v_tid_2127_ = lean_ctor_get_uint64(v_traceState_2115_, sizeof(void*)*1);
v_traces_2128_ = lean_ctor_get(v_traceState_2115_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_traceState_2115_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2130_ = v_traceState_2115_;
v_isShared_2131_ = v_isSharedCheck_2141_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_traces_2128_);
lean_dec(v_traceState_2115_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2141_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2059_, v_traces_2128_);
lean_dec_ref(v_traces_2128_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2132_);
v___x_2134_ = v___x_2130_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2132_);
lean_ctor_set_uint64(v_reuseFailAlloc_2140_, sizeof(void*)*1, v_tid_2127_);
v___x_2134_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v___x_2134_);
v___x_2136_ = v___x_2125_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_env_2116_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_nextMacroScope_2117_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_ngen_2118_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_auxDeclNGen_2119_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2139_, 5, v_cache_2120_);
lean_ctor_set(v_reuseFailAlloc_2139_, 6, v_messages_2121_);
lean_ctor_set(v_reuseFailAlloc_2139_, 7, v_infoState_2122_);
lean_ctor_set(v_reuseFailAlloc_2139_, 8, v_snapshotTasks_2123_);
v___x_2136_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_st_ref_set(v___y_2067_, v___x_2136_);
v___x_2138_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(v_fst_2069_);
return v___x_2138_;
}
}
}
}
}
else
{
goto v___jp_2107_;
}
}
else
{
goto v___jp_2107_;
}
}
v___jp_2143_:
{
double v___x_2145_; double v___x_2146_; double v___x_2147_; uint8_t v___x_2148_; 
v___x_2145_ = lean_unbox_float(v_snd_2081_);
v___x_2146_ = lean_unbox_float(v_fst_2080_);
v___x_2147_ = lean_float_sub(v___x_2145_, v___x_2146_);
v___x_2148_ = lean_float_decLt(v___y_2144_, v___x_2147_);
v___y_2113_ = v___x_2148_;
goto v___jp_2112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object* v_cls_2161_, lean_object* v_collapsed_2162_, lean_object* v_tag_2163_, lean_object* v_opts_2164_, lean_object* v_clsEnabled_2165_, lean_object* v_oldTraces_2166_, lean_object* v_msg_2167_, lean_object* v_resStartStop_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v_collapsed_boxed_2176_; uint8_t v_clsEnabled_boxed_2177_; lean_object* v_res_2178_; 
v_collapsed_boxed_2176_ = lean_unbox(v_collapsed_2162_);
v_clsEnabled_boxed_2177_ = lean_unbox(v_clsEnabled_2165_);
v_res_2178_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_cls_2161_, v_collapsed_boxed_2176_, v_tag_2163_, v_opts_2164_, v_clsEnabled_boxed_2177_, v_oldTraces_2166_, v_msg_2167_, v_resStartStop_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec_ref(v_opts_2164_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
lean_object* v_ks_2183_; lean_object* v_vs_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2208_; 
v_ks_2183_ = lean_ctor_get(v_x_2179_, 0);
v_vs_2184_ = lean_ctor_get(v_x_2179_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2179_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2186_ = v_x_2179_;
v_isShared_2187_ = v_isSharedCheck_2208_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_vs_2184_);
lean_inc(v_ks_2183_);
lean_dec(v_x_2179_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2208_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = lean_array_get_size(v_ks_2183_);
v___x_2189_ = lean_nat_dec_lt(v_x_2180_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
lean_dec(v_x_2180_);
v___x_2190_ = lean_array_push(v_ks_2183_, v_x_2181_);
v___x_2191_ = lean_array_push(v_vs_2184_, v_x_2182_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2191_);
lean_ctor_set(v___x_2186_, 0, v___x_2190_);
v___x_2193_ = v___x_2186_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
else
{
lean_object* v_k_x27_2195_; uint8_t v___x_2196_; 
v_k_x27_2195_ = lean_array_fget_borrowed(v_ks_2183_, v_x_2180_);
v___x_2196_ = l_Lean_instBEqMVarId_beq(v_x_2181_, v_k_x27_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2198_; 
if (v_isShared_2187_ == 0)
{
v___x_2198_ = v___x_2186_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_ks_2183_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_vs_2184_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_add(v_x_2180_, v___x_2199_);
lean_dec(v_x_2180_);
v_x_2179_ = v___x_2198_;
v_x_2180_ = v___x_2200_;
goto _start;
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2203_ = lean_array_fset(v_ks_2183_, v_x_2180_, v_x_2181_);
v___x_2204_ = lean_array_fset(v_vs_2184_, v_x_2180_, v_x_2182_);
lean_dec(v_x_2180_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2204_);
lean_ctor_set(v___x_2186_, 0, v___x_2203_);
v___x_2206_ = v___x_2186_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_n_2209_, lean_object* v_k_2210_, lean_object* v_v_2211_){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_n_2209_, v___x_2212_, v_k_2210_, v_v_2211_);
return v___x_2213_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; 
v___x_2214_ = ((size_t)5ULL);
v___x_2215_ = ((size_t)1ULL);
v___x_2216_ = lean_usize_shift_left(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; 
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_2219_ = lean_usize_sub(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2221_, size_t v_x_2222_, size_t v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 0)
{
lean_object* v_es_2226_; size_t v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; size_t v___x_2230_; lean_object* v_j_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v_es_2226_ = lean_ctor_get(v_x_2221_, 0);
v___x_2227_ = ((size_t)5ULL);
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1);
v___x_2230_ = lean_usize_land(v_x_2222_, v___x_2229_);
v_j_2231_ = lean_usize_to_nat(v___x_2230_);
v___x_2232_ = lean_array_get_size(v_es_2226_);
v___x_2233_ = lean_nat_dec_lt(v_j_2231_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_dec(v_j_2231_);
lean_dec(v_x_2225_);
lean_dec(v_x_2224_);
return v_x_2221_;
}
else
{
lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2270_; 
lean_inc_ref(v_es_2226_);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; 
v_unused_2271_ = lean_ctor_get(v_x_2221_, 0);
lean_dec(v_unused_2271_);
v___x_2235_ = v_x_2221_;
v_isShared_2236_ = v_isSharedCheck_2270_;
goto v_resetjp_2234_;
}
else
{
lean_dec(v_x_2221_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2270_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v_v_2237_; lean_object* v___x_2238_; lean_object* v_xs_x27_2239_; lean_object* v___y_2241_; 
v_v_2237_ = lean_array_fget(v_es_2226_, v_j_2231_);
v___x_2238_ = lean_box(0);
v_xs_x27_2239_ = lean_array_fset(v_es_2226_, v_j_2231_, v___x_2238_);
switch(lean_obj_tag(v_v_2237_))
{
case 0:
{
lean_object* v_key_2246_; lean_object* v_val_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2257_; 
v_key_2246_ = lean_ctor_get(v_v_2237_, 0);
v_val_2247_ = lean_ctor_get(v_v_2237_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_v_2237_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2249_ = v_v_2237_;
v_isShared_2250_ = v_isSharedCheck_2257_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_val_2247_);
lean_inc(v_key_2246_);
lean_dec(v_v_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2257_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
uint8_t v___x_2251_; 
v___x_2251_ = l_Lean_instBEqMVarId_beq(v_x_2224_, v_key_2246_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_del_object(v___x_2249_);
v___x_2252_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2246_, v_val_2247_, v_x_2224_, v_x_2225_);
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
v___y_2241_ = v___x_2253_;
goto v___jp_2240_;
}
else
{
lean_object* v___x_2255_; 
lean_dec(v_val_2247_);
lean_dec(v_key_2246_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v_x_2225_);
lean_ctor_set(v___x_2249_, 0, v_x_2224_);
v___x_2255_ = v___x_2249_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_x_2224_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_x_2225_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
v___y_2241_ = v___x_2255_;
goto v___jp_2240_;
}
}
}
}
case 1:
{
lean_object* v_node_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2268_; 
v_node_2258_ = lean_ctor_get(v_v_2237_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_v_2237_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2260_ = v_v_2237_;
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_node_2258_);
lean_dec(v_v_2237_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
size_t v___x_2262_; size_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2262_ = lean_usize_shift_right(v_x_2222_, v___x_2227_);
v___x_2263_ = lean_usize_add(v_x_2223_, v___x_2228_);
v___x_2264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_node_2258_, v___x_2262_, v___x_2263_, v_x_2224_, v_x_2225_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2264_);
v___x_2266_ = v___x_2260_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
v___y_2241_ = v___x_2266_;
goto v___jp_2240_;
}
}
}
default: 
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_x_2224_);
lean_ctor_set(v___x_2269_, 1, v_x_2225_);
v___y_2241_ = v___x_2269_;
goto v___jp_2240_;
}
}
v___jp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = lean_array_fset(v_xs_x27_2239_, v_j_2231_, v___y_2241_);
lean_dec(v_j_2231_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2242_);
v___x_2244_ = v___x_2235_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
else
{
lean_object* v_ks_2272_; lean_object* v_vs_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2293_; 
v_ks_2272_ = lean_ctor_get(v_x_2221_, 0);
v_vs_2273_ = lean_ctor_get(v_x_2221_, 1);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2275_ = v_x_2221_;
v_isShared_2276_ = v_isSharedCheck_2293_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_vs_2273_);
lean_inc(v_ks_2272_);
lean_dec(v_x_2221_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2293_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_ks_2272_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_vs_2273_);
v___x_2278_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v_newNode_2279_; uint8_t v___y_2281_; size_t v___x_2287_; uint8_t v___x_2288_; 
v_newNode_2279_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v___x_2278_, v_x_2224_, v_x_2225_);
v___x_2287_ = ((size_t)7ULL);
v___x_2288_ = lean_usize_dec_le(v___x_2287_, v_x_2223_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2279_);
v___x_2290_ = lean_unsigned_to_nat(4u);
v___x_2291_ = lean_nat_dec_lt(v___x_2289_, v___x_2290_);
lean_dec(v___x_2289_);
v___y_2281_ = v___x_2291_;
goto v___jp_2280_;
}
else
{
v___y_2281_ = v___x_2288_;
goto v___jp_2280_;
}
v___jp_2280_:
{
if (v___y_2281_ == 0)
{
lean_object* v_ks_2282_; lean_object* v_vs_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_ks_2282_ = lean_ctor_get(v_newNode_2279_, 0);
lean_inc_ref(v_ks_2282_);
v_vs_2283_ = lean_ctor_get(v_newNode_2279_, 1);
lean_inc_ref(v_vs_2283_);
lean_dec_ref(v_newNode_2279_);
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__2);
v___x_2286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_x_2223_, v_ks_2282_, v_vs_2283_, v___x_2284_, v___x_2285_);
lean_dec_ref(v_vs_2283_);
lean_dec_ref(v_ks_2282_);
return v___x_2286_;
}
else
{
return v_newNode_2279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t v_depth_2294_, lean_object* v_keys_2295_, lean_object* v_vals_2296_, lean_object* v_i_2297_, lean_object* v_entries_2298_){
_start:
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_array_get_size(v_keys_2295_);
v___x_2300_ = lean_nat_dec_lt(v_i_2297_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_dec(v_i_2297_);
return v_entries_2298_;
}
else
{
lean_object* v_k_2301_; lean_object* v_v_2302_; uint64_t v___x_2303_; size_t v_h_2304_; size_t v___x_2305_; lean_object* v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v_h_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_k_2301_ = lean_array_fget_borrowed(v_keys_2295_, v_i_2297_);
v_v_2302_ = lean_array_fget_borrowed(v_vals_2296_, v_i_2297_);
v___x_2303_ = l_Lean_instHashableMVarId_hash(v_k_2301_);
v_h_2304_ = lean_uint64_to_usize(v___x_2303_);
v___x_2305_ = ((size_t)5ULL);
v___x_2306_ = lean_unsigned_to_nat(1u);
v___x_2307_ = ((size_t)1ULL);
v___x_2308_ = lean_usize_sub(v_depth_2294_, v___x_2307_);
v___x_2309_ = lean_usize_mul(v___x_2305_, v___x_2308_);
v_h_2310_ = lean_usize_shift_right(v_h_2304_, v___x_2309_);
v___x_2311_ = lean_nat_add(v_i_2297_, v___x_2306_);
lean_dec(v_i_2297_);
lean_inc(v_v_2302_);
lean_inc(v_k_2301_);
v___x_2312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_entries_2298_, v_h_2310_, v_depth_2294_, v_k_2301_, v_v_2302_);
v_i_2297_ = v___x_2311_;
v_entries_2298_ = v___x_2312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_depth_2314_, lean_object* v_keys_2315_, lean_object* v_vals_2316_, lean_object* v_i_2317_, lean_object* v_entries_2318_){
_start:
{
size_t v_depth_boxed_2319_; lean_object* v_res_2320_; 
v_depth_boxed_2319_ = lean_unbox_usize(v_depth_2314_);
lean_dec(v_depth_2314_);
v_res_2320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_boxed_2319_, v_keys_2315_, v_vals_2316_, v_i_2317_, v_entries_2318_);
lean_dec_ref(v_vals_2316_);
lean_dec_ref(v_keys_2315_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_2321_, lean_object* v_x_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_){
_start:
{
size_t v_x_18929__boxed_2326_; size_t v_x_18930__boxed_2327_; lean_object* v_res_2328_; 
v_x_18929__boxed_2326_ = lean_unbox_usize(v_x_2322_);
lean_dec(v_x_2322_);
v_x_18930__boxed_2327_ = lean_unbox_usize(v_x_2323_);
lean_dec(v_x_2323_);
v_res_2328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2321_, v_x_18929__boxed_2326_, v_x_18930__boxed_2327_, v_x_2324_, v_x_2325_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object* v_x_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_){
_start:
{
uint64_t v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; lean_object* v___x_2335_; 
v___x_2332_ = l_Lean_instHashableMVarId_hash(v_x_2330_);
v___x_2333_ = lean_uint64_to_usize(v___x_2332_);
v___x_2334_ = ((size_t)1ULL);
v___x_2335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2329_, v___x_2333_, v___x_2334_, v_x_2330_, v_x_2331_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v_mvarId_2336_, lean_object* v_val_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v_mctx_2341_; lean_object* v_cache_2342_; lean_object* v_zetaDeltaFVarIds_2343_; lean_object* v_postponed_2344_; lean_object* v_diag_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2373_; 
v___x_2340_ = lean_st_ref_take(v___y_2338_);
v_mctx_2341_ = lean_ctor_get(v___x_2340_, 0);
v_cache_2342_ = lean_ctor_get(v___x_2340_, 1);
v_zetaDeltaFVarIds_2343_ = lean_ctor_get(v___x_2340_, 2);
v_postponed_2344_ = lean_ctor_get(v___x_2340_, 3);
v_diag_2345_ = lean_ctor_get(v___x_2340_, 4);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2347_ = v___x_2340_;
v_isShared_2348_ = v_isSharedCheck_2373_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_diag_2345_);
lean_inc(v_postponed_2344_);
lean_inc(v_zetaDeltaFVarIds_2343_);
lean_inc(v_cache_2342_);
lean_inc(v_mctx_2341_);
lean_dec(v___x_2340_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2373_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v_depth_2349_; lean_object* v_levelAssignDepth_2350_; lean_object* v_lmvarCounter_2351_; lean_object* v_mvarCounter_2352_; lean_object* v_lDecls_2353_; lean_object* v_decls_2354_; lean_object* v_userNames_2355_; lean_object* v_lAssignment_2356_; lean_object* v_eAssignment_2357_; lean_object* v_dAssignment_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2372_; 
v_depth_2349_ = lean_ctor_get(v_mctx_2341_, 0);
v_levelAssignDepth_2350_ = lean_ctor_get(v_mctx_2341_, 1);
v_lmvarCounter_2351_ = lean_ctor_get(v_mctx_2341_, 2);
v_mvarCounter_2352_ = lean_ctor_get(v_mctx_2341_, 3);
v_lDecls_2353_ = lean_ctor_get(v_mctx_2341_, 4);
v_decls_2354_ = lean_ctor_get(v_mctx_2341_, 5);
v_userNames_2355_ = lean_ctor_get(v_mctx_2341_, 6);
v_lAssignment_2356_ = lean_ctor_get(v_mctx_2341_, 7);
v_eAssignment_2357_ = lean_ctor_get(v_mctx_2341_, 8);
v_dAssignment_2358_ = lean_ctor_get(v_mctx_2341_, 9);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_mctx_2341_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2360_ = v_mctx_2341_;
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_dAssignment_2358_);
lean_inc(v_eAssignment_2357_);
lean_inc(v_lAssignment_2356_);
lean_inc(v_userNames_2355_);
lean_inc(v_decls_2354_);
lean_inc(v_lDecls_2353_);
lean_inc(v_mvarCounter_2352_);
lean_inc(v_lmvarCounter_2351_);
lean_inc(v_levelAssignDepth_2350_);
lean_inc(v_depth_2349_);
lean_dec(v_mctx_2341_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_eAssignment_2357_, v_mvarId_2336_, v_val_2337_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 8, v___x_2362_);
v___x_2364_ = v___x_2360_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_depth_2349_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_levelAssignDepth_2350_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_lmvarCounter_2351_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_mvarCounter_2352_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_lDecls_2353_);
lean_ctor_set(v_reuseFailAlloc_2371_, 5, v_decls_2354_);
lean_ctor_set(v_reuseFailAlloc_2371_, 6, v_userNames_2355_);
lean_ctor_set(v_reuseFailAlloc_2371_, 7, v_lAssignment_2356_);
lean_ctor_set(v_reuseFailAlloc_2371_, 8, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2371_, 9, v_dAssignment_2358_);
v___x_2364_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2364_);
v___x_2366_ = v___x_2347_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_cache_2342_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_zetaDeltaFVarIds_2343_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_postponed_2344_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_diag_2345_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_st_ref_set(v___y_2338_, v___x_2366_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object* v_mvarId_2374_, lean_object* v_val_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2374_, v_val_2375_, v___y_2376_);
lean_dec(v___y_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_keys_2379_, lean_object* v_i_2380_, lean_object* v_k_2381_){
_start:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = lean_array_get_size(v_keys_2379_);
v___x_2383_ = lean_nat_dec_lt(v_i_2380_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_dec(v_i_2380_);
return v___x_2383_;
}
else
{
lean_object* v_k_x27_2384_; uint8_t v___x_2385_; 
v_k_x27_2384_ = lean_array_fget_borrowed(v_keys_2379_, v_i_2380_);
v___x_2385_ = l_Lean_instBEqMVarId_beq(v_k_2381_, v_k_x27_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_unsigned_to_nat(1u);
v___x_2387_ = lean_nat_add(v_i_2380_, v___x_2386_);
lean_dec(v_i_2380_);
v_i_2380_ = v___x_2387_;
goto _start;
}
else
{
lean_dec(v_i_2380_);
return v___x_2385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_keys_2389_, lean_object* v_i_2390_, lean_object* v_k_2391_){
_start:
{
uint8_t v_res_2392_; lean_object* v_r_2393_; 
v_res_2392_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2389_, v_i_2390_, v_k_2391_);
lean_dec(v_k_2391_);
lean_dec_ref(v_keys_2389_);
v_r_2393_ = lean_box(v_res_2392_);
return v_r_2393_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(lean_object* v_x_2394_, size_t v_x_2395_, lean_object* v_x_2396_){
_start:
{
if (lean_obj_tag(v_x_2394_) == 0)
{
lean_object* v_es_2397_; lean_object* v___x_2398_; size_t v___x_2399_; size_t v___x_2400_; size_t v___x_2401_; lean_object* v_j_2402_; lean_object* v___x_2403_; 
v_es_2397_ = lean_ctor_get(v_x_2394_, 0);
v___x_2398_ = lean_box(2);
v___x_2399_ = ((size_t)5ULL);
v___x_2400_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__1);
v___x_2401_ = lean_usize_land(v_x_2395_, v___x_2400_);
v_j_2402_ = lean_usize_to_nat(v___x_2401_);
v___x_2403_ = lean_array_get_borrowed(v___x_2398_, v_es_2397_, v_j_2402_);
lean_dec(v_j_2402_);
switch(lean_obj_tag(v___x_2403_))
{
case 0:
{
lean_object* v_key_2404_; uint8_t v___x_2405_; 
v_key_2404_ = lean_ctor_get(v___x_2403_, 0);
v___x_2405_ = l_Lean_instBEqMVarId_beq(v_x_2396_, v_key_2404_);
return v___x_2405_;
}
case 1:
{
lean_object* v_node_2406_; size_t v___x_2407_; 
v_node_2406_ = lean_ctor_get(v___x_2403_, 0);
v___x_2407_ = lean_usize_shift_right(v_x_2395_, v___x_2399_);
v_x_2394_ = v_node_2406_;
v_x_2395_ = v___x_2407_;
goto _start;
}
default: 
{
uint8_t v___x_2409_; 
v___x_2409_ = 0;
return v___x_2409_;
}
}
}
else
{
lean_object* v_ks_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v_ks_2410_ = lean_ctor_get(v_x_2394_, 0);
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_ks_2410_, v___x_2411_, v_x_2396_);
return v___x_2412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_2413_, lean_object* v_x_2414_, lean_object* v_x_2415_){
_start:
{
size_t v_x_19167__boxed_2416_; uint8_t v_res_2417_; lean_object* v_r_2418_; 
v_x_19167__boxed_2416_ = lean_unbox_usize(v_x_2414_);
lean_dec(v_x_2414_);
v_res_2417_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2413_, v_x_19167__boxed_2416_, v_x_2415_);
lean_dec(v_x_2415_);
lean_dec_ref(v_x_2413_);
v_r_2418_ = lean_box(v_res_2417_);
return v_r_2418_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(lean_object* v_x_2419_, lean_object* v_x_2420_){
_start:
{
uint64_t v___x_2421_; size_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2421_ = l_Lean_instHashableMVarId_hash(v_x_2420_);
v___x_2422_ = lean_uint64_to_usize(v___x_2421_);
v___x_2423_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2419_, v___x_2422_, v_x_2420_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg___boxed(lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
uint8_t v_res_2426_; lean_object* v_r_2427_; 
v_res_2426_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2424_, v_x_2425_);
lean_dec(v_x_2425_);
lean_dec_ref(v_x_2424_);
v_r_2427_ = lean_box(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(lean_object* v_mvarId_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v_mctx_2432_; lean_object* v_eAssignment_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2431_ = lean_st_ref_get(v___y_2429_);
v_mctx_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc_ref(v_mctx_2432_);
lean_dec(v___x_2431_);
v_eAssignment_2433_ = lean_ctor_get(v_mctx_2432_, 8);
lean_inc_ref(v_eAssignment_2433_);
lean_dec_ref(v_mctx_2432_);
v___x_2434_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_eAssignment_2433_, v_mvarId_2428_);
lean_dec_ref(v_eAssignment_2433_);
v___x_2435_ = lean_box(v___x_2434_);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg___boxed(lean_object* v_mvarId_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec(v_mvarId_2437_);
return v_res_2440_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2441_; double v___x_2442_; 
v___x_2441_ = lean_unsigned_to_nat(1000000000u);
v___x_2442_ = lean_float_of_nat(v___x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1));
v___x_2445_ = l_Lean_stringToMessageData(v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(lean_object* v___x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v___x_2446_, v___y_2450_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2624_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2624_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2624_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_unbox(v_a_2455_);
lean_dec(v_a_2455_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
lean_del_object(v___x_2457_);
lean_inc(v___x_2446_);
v___x_2460_ = l_Lean_MVarId_getType(v___x_2446_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_options_2461_; uint8_t v_hasTrace_2462_; 
v_options_2461_ = lean_ctor_get(v___y_2451_, 2);
v_hasTrace_2462_ = lean_ctor_get_uint8(v_options_2461_, sizeof(void*)*1);
if (v_hasTrace_2462_ == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2460_);
v___x_2464_ = l_Lean_Meta_mkDefault(v_a_2463_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2446_, v_a_2465_, v___y_2450_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2474_; 
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2466_, 0);
lean_dec(v_unused_2475_);
v___x_2468_ = v___x_2466_;
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
else
{
lean_dec(v___x_2466_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2470_ = lean_box(0);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2470_);
v___x_2472_ = v___x_2468_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
return v___x_2466_;
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec(v___x_2446_);
v_a_2476_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2464_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2464_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v_inheritedTraceOptions_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v_a_2494_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v_a_2509_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v_a_2514_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v_a_2525_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v_a_2537_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v_a_2542_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; 
v_a_2484_ = lean_ctor_get(v___x_2460_, 0);
lean_inc_n(v_a_2484_, 2);
lean_dec_ref(v___x_2460_);
v_inheritedTraceOptions_2485_ = lean_ctor_get(v___y_2451_, 13);
v___f_2486_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2486_, 0, v_a_2484_);
v___x_2487_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2488_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_2489_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2485_, v_options_2461_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2585_ = l_Lean_trace_profiler;
v___x_2586_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2461_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
lean_dec_ref(v___f_2486_);
v___x_2587_ = l_Lean_Meta_mkDefault(v_a_2484_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2589_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc_n(v_a_2588_, 2);
lean_dec_ref(v___x_2587_);
v___x_2589_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2446_, v_a_2588_, v___y_2450_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2602_; 
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v___x_2589_, 0);
lean_dec(v_unused_2603_);
v___x_2591_ = v___x_2589_;
v_isShared_2592_ = v_isSharedCheck_2602_;
goto v_resetjp_2590_;
}
else
{
lean_dec(v___x_2589_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2602_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
if (v___x_2490_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_a_2588_);
v___x_2593_ = lean_box(0);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_del_object(v___x_2591_);
v___x_2597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2598_ = lean_unsigned_to_nat(30u);
v___x_2599_ = l_Lean_inlineExprTrailing(v_a_2588_, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2597_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2487_, v___x_2600_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2601_;
}
}
}
else
{
lean_dec(v_a_2588_);
return v___x_2589_;
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v___x_2446_);
v_a_2604_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2587_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2587_);
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
else
{
goto v___jp_2550_;
}
}
else
{
goto v___jp_2550_;
}
v___jp_2491_:
{
lean_object* v___x_2495_; double v___x_2496_; double v___x_2497_; double v___x_2498_; double v___x_2499_; double v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2495_ = lean_io_mono_nanos_now();
v___x_2496_ = lean_float_of_nat(v___y_2493_);
v___x_2497_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_2498_ = lean_float_div(v___x_2496_, v___x_2497_);
v___x_2499_ = lean_float_of_nat(v___x_2495_);
v___x_2500_ = lean_float_div(v___x_2499_, v___x_2497_);
v___x_2501_ = lean_box_float(v___x_2498_);
v___x_2502_ = lean_box_float(v___x_2500_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2494_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2487_, v_hasTrace_2462_, v___x_2488_, v_options_2461_, v___x_2490_, v___y_2492_, v___f_2486_, v___x_2504_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2505_;
}
v___jp_2506_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_a_2509_);
v___y_2492_ = v___y_2507_;
v___y_2493_ = v___y_2508_;
v_a_2494_ = v___x_2510_;
goto v___jp_2491_;
}
v___jp_2511_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_a_2514_);
v___y_2492_ = v___y_2512_;
v___y_2493_ = v___y_2513_;
v_a_2494_ = v___x_2515_;
goto v___jp_2491_;
}
v___jp_2516_:
{
if (lean_obj_tag(v___y_2519_) == 0)
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___y_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref(v___y_2519_);
v___y_2512_ = v___y_2517_;
v___y_2513_ = v___y_2518_;
v_a_2514_ = v_a_2520_;
goto v___jp_2511_;
}
else
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___y_2519_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___y_2519_);
v___y_2507_ = v___y_2517_;
v___y_2508_ = v___y_2518_;
v_a_2509_ = v_a_2521_;
goto v___jp_2506_;
}
}
v___jp_2522_:
{
lean_object* v___x_2526_; double v___x_2527_; double v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2526_ = lean_io_get_num_heartbeats();
v___x_2527_ = lean_float_of_nat(v___y_2524_);
v___x_2528_ = lean_float_of_nat(v___x_2526_);
v___x_2529_ = lean_box_float(v___x_2527_);
v___x_2530_ = lean_box_float(v___x_2528_);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v_a_2525_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2487_, v_hasTrace_2462_, v___x_2488_, v_options_2461_, v___x_2490_, v___y_2523_, v___f_2486_, v___x_2532_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2533_;
}
v___jp_2534_:
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_a_2537_);
v___y_2523_ = v___y_2535_;
v___y_2524_ = v___y_2536_;
v_a_2525_ = v___x_2538_;
goto v___jp_2522_;
}
v___jp_2539_:
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_a_2542_);
v___y_2523_ = v___y_2540_;
v___y_2524_ = v___y_2541_;
v_a_2525_ = v___x_2543_;
goto v___jp_2522_;
}
v___jp_2544_:
{
if (lean_obj_tag(v___y_2547_) == 0)
{
lean_object* v_a_2548_; 
v_a_2548_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___y_2547_);
v___y_2540_ = v___y_2545_;
v___y_2541_ = v___y_2546_;
v_a_2542_ = v_a_2548_;
goto v___jp_2539_;
}
else
{
lean_object* v_a_2549_; 
v_a_2549_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___y_2547_);
v___y_2535_ = v___y_2545_;
v___y_2536_ = v___y_2546_;
v_a_2537_ = v_a_2549_;
goto v___jp_2534_;
}
}
v___jp_2550_:
{
lean_object* v___x_2551_; 
v___x_2551_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_2452_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2554_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2461_, v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_io_mono_nanos_now();
v___x_2556_ = l_Lean_Meta_mkDefault(v_a_2484_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_n(v_a_2557_, 2);
lean_dec_ref(v___x_2556_);
v___x_2558_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2446_, v_a_2557_, v___y_2450_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref(v___x_2558_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2559_; 
lean_dec(v_a_2557_);
v___x_2559_ = lean_box(0);
v___y_2512_ = v_a_2552_;
v___y_2513_ = v___x_2555_;
v_a_2514_ = v___x_2559_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2560_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2561_ = lean_unsigned_to_nat(30u);
v___x_2562_ = l_Lean_inlineExprTrailing(v_a_2557_, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2560_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2487_, v___x_2563_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
v___y_2517_ = v_a_2552_;
v___y_2518_ = v___x_2555_;
v___y_2519_ = v___x_2564_;
goto v___jp_2516_;
}
}
else
{
lean_dec(v_a_2557_);
v___y_2517_ = v_a_2552_;
v___y_2518_ = v___x_2555_;
v___y_2519_ = v___x_2558_;
goto v___jp_2516_;
}
}
else
{
lean_object* v_a_2565_; 
lean_dec(v___x_2446_);
v_a_2565_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2565_);
lean_dec_ref(v___x_2556_);
v___y_2507_ = v_a_2552_;
v___y_2508_ = v___x_2555_;
v_a_2509_ = v_a_2565_;
goto v___jp_2506_;
}
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = lean_io_get_num_heartbeats();
v___x_2567_ = l_Lean_Meta_mkDefault(v_a_2484_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_n(v_a_2568_, 2);
lean_dec_ref(v___x_2567_);
v___x_2569_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2446_, v_a_2568_, v___y_2450_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_dec_ref(v___x_2569_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2570_; 
lean_dec(v_a_2568_);
v___x_2570_ = lean_box(0);
v___y_2540_ = v_a_2552_;
v___y_2541_ = v___x_2566_;
v_a_2542_ = v___x_2570_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2571_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2572_ = lean_unsigned_to_nat(30u);
v___x_2573_ = l_Lean_inlineExprTrailing(v_a_2568_, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2571_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2487_, v___x_2574_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
v___y_2545_ = v_a_2552_;
v___y_2546_ = v___x_2566_;
v___y_2547_ = v___x_2575_;
goto v___jp_2544_;
}
}
else
{
lean_dec(v_a_2568_);
v___y_2545_ = v_a_2552_;
v___y_2546_ = v___x_2566_;
v___y_2547_ = v___x_2569_;
goto v___jp_2544_;
}
}
else
{
lean_object* v_a_2576_; 
lean_dec(v___x_2446_);
v_a_2576_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2567_);
v___y_2535_ = v_a_2552_;
v___y_2536_ = v___x_2566_;
v_a_2537_ = v_a_2576_;
goto v___jp_2534_;
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v___f_2486_);
lean_dec(v_a_2484_);
lean_dec(v___x_2446_);
v_a_2577_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2551_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2551_);
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
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v___x_2446_);
v_a_2612_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2460_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2460_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_dec(v___x_2446_);
v___x_2620_ = lean_box(0);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2620_);
v___x_2622_ = v___x_2457_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v___x_2446_);
v_a_2625_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2454_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2454_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2642_, size_t v_i_2643_, size_t v_stop_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v___x_2653_; 
v___x_2653_ = lean_usize_dec_eq(v_i_2643_, v_stop_2644_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v___f_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_array_uget_borrowed(v_as_2642_, v_i_2643_);
lean_inc_n(v___x_2654_, 2);
v___f_2655_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2655_, 0, v___x_2654_);
v___x_2656_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2654_, v___f_2655_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; size_t v___x_2658_; size_t v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
v___x_2658_ = ((size_t)1ULL);
v___x_2659_ = lean_usize_add(v_i_2643_, v___x_2658_);
v_i_2643_ = v___x_2659_;
v_b_2645_ = v_a_2657_;
goto _start;
}
else
{
return v___x_2656_;
}
}
else
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v_b_2645_);
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2662_, lean_object* v_i_2663_, lean_object* v_stop_2664_, lean_object* v_b_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
size_t v_i_boxed_2673_; size_t v_stop_boxed_2674_; lean_object* v_res_2675_; 
v_i_boxed_2673_ = lean_unbox_usize(v_i_2663_);
lean_dec(v_i_2663_);
v_stop_boxed_2674_ = lean_unbox_usize(v_stop_2664_);
lean_dec(v_stop_2664_);
v_res_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2662_, v_i_boxed_2673_, v_stop_boxed_2674_, v_b_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec_ref(v_as_2662_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2676_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2706_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2706_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2706_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_array_get_size(v_a_2685_);
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_nat_dec_lt(v___x_2689_, v___x_2690_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2694_; 
lean_dec(v_a_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2691_);
v___x_2694_ = v___x_2687_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2691_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
else
{
uint8_t v___x_2696_; 
v___x_2696_ = lean_nat_dec_le(v___x_2690_, v___x_2690_);
if (v___x_2696_ == 0)
{
if (v___x_2692_ == 0)
{
lean_object* v___x_2698_; 
lean_dec(v_a_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2691_);
v___x_2698_ = v___x_2687_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2691_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
else
{
size_t v___x_2700_; size_t v___x_2701_; lean_object* v___x_2702_; 
lean_del_object(v___x_2687_);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = lean_usize_of_nat(v___x_2690_);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2685_, v___x_2700_, v___x_2701_, v___x_2691_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2685_);
return v___x_2702_;
}
}
else
{
size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
lean_del_object(v___x_2687_);
v___x_2703_ = ((size_t)0ULL);
v___x_2704_ = lean_usize_of_nat(v___x_2690_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2685_, v___x_2703_, v___x_2704_, v___x_2691_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2685_);
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_a_2707_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2684_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2684_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2724_, v___y_2728_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v_mvarId_2733_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v_mvarId_2742_, lean_object* v_val_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2742_, v_val_2743_, v___y_2747_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v_mvarId_2752_, lean_object* v_val_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2752_, v_val_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(lean_object* v_00_u03b1_2762_, lean_object* v_x_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(v_x_2763_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2772_, lean_object* v_x_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_00_u03b1_2772_, v_x_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
return v_res_2781_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_){
_start:
{
uint8_t v___x_2785_; 
v___x_2785_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2783_, v_x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
uint8_t v_res_2789_; lean_object* v_r_2790_; 
v_res_2789_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2786_, v_x_2787_, v_x_2788_);
lean_dec(v_x_2788_);
lean_dec_ref(v_x_2787_);
v_r_2790_ = lean_box(v_res_2789_);
return v_r_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object* v_00_u03b2_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_x_2792_, v_x_2793_, v_x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object* v_oldTraces_2796_, lean_object* v_data_2797_, lean_object* v_ref_2798_, lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_oldTraces_2796_, v_data_2797_, v_ref_2798_, v_msg_2799_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object* v_oldTraces_2808_, lean_object* v_data_2809_, lean_object* v_ref_2810_, lean_object* v_msg_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(v_oldTraces_2808_, v_data_2809_, v_ref_2810_, v_msg_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2819_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2820_, lean_object* v_x_2821_, size_t v_x_2822_, lean_object* v_x_2823_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2821_, v_x_2822_, v_x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_){
_start:
{
size_t v_x_19868__boxed_2829_; uint8_t v_res_2830_; lean_object* v_r_2831_; 
v_x_19868__boxed_2829_ = lean_unbox_usize(v_x_2827_);
lean_dec(v_x_2827_);
v_res_2830_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2825_, v_x_2826_, v_x_19868__boxed_2829_, v_x_2828_);
lean_dec(v_x_2828_);
lean_dec_ref(v_x_2826_);
v_r_2831_ = lean_box(v_res_2830_);
return v_r_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2832_, lean_object* v_x_2833_, size_t v_x_2834_, size_t v_x_2835_, lean_object* v_x_2836_, lean_object* v_x_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2833_, v_x_2834_, v_x_2835_, v_x_2836_, v_x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2839_, lean_object* v_x_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
size_t v_x_19879__boxed_2845_; size_t v_x_19880__boxed_2846_; lean_object* v_res_2847_; 
v_x_19879__boxed_2845_ = lean_unbox_usize(v_x_2841_);
lean_dec(v_x_2841_);
v_x_19880__boxed_2846_ = lean_unbox_usize(v_x_2842_);
lean_dec(v_x_2842_);
v_res_2847_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(v_00_u03b2_2839_, v_x_2840_, v_x_19879__boxed_2845_, v_x_19880__boxed_2846_, v_x_2843_, v_x_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2848_, lean_object* v_keys_2849_, lean_object* v_vals_2850_, lean_object* v_heq_2851_, lean_object* v_i_2852_, lean_object* v_k_2853_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2849_, v_i_2852_, v_k_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2855_, lean_object* v_keys_2856_, lean_object* v_vals_2857_, lean_object* v_heq_2858_, lean_object* v_i_2859_, lean_object* v_k_2860_){
_start:
{
uint8_t v_res_2861_; lean_object* v_r_2862_; 
v_res_2861_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2855_, v_keys_2856_, v_vals_2857_, v_heq_2858_, v_i_2859_, v_k_2860_);
lean_dec(v_k_2860_);
lean_dec_ref(v_vals_2857_);
lean_dec_ref(v_keys_2856_);
v_r_2862_ = lean_box(v_res_2861_);
return v_r_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_2863_, lean_object* v_n_2864_, lean_object* v_k_2865_, lean_object* v_v_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v_n_2864_, v_k_2865_, v_v_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b2_2868_, size_t v_depth_2869_, lean_object* v_keys_2870_, lean_object* v_vals_2871_, lean_object* v_heq_2872_, lean_object* v_i_2873_, lean_object* v_entries_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2869_, v_keys_2870_, v_vals_2871_, v_i_2873_, v_entries_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b2_2876_, lean_object* v_depth_2877_, lean_object* v_keys_2878_, lean_object* v_vals_2879_, lean_object* v_heq_2880_, lean_object* v_i_2881_, lean_object* v_entries_2882_){
_start:
{
size_t v_depth_boxed_2883_; lean_object* v_res_2884_; 
v_depth_boxed_2883_ = lean_unbox_usize(v_depth_2877_);
lean_dec(v_depth_2877_);
v_res_2884_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(v_00_u03b2_2876_, v_depth_boxed_2883_, v_keys_2878_, v_vals_2879_, v_heq_2880_, v_i_2881_, v_entries_2882_);
lean_dec_ref(v_vals_2879_);
lean_dec_ref(v_keys_2878_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_x_2886_, v_x_2887_, v_x_2888_, v_x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v___x_2894_; 
v___x_2894_ = l_Lean_Expr_hasMVar(v_e_2891_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_e_2891_);
return v___x_2895_;
}
else
{
lean_object* v___x_2896_; lean_object* v_mctx_2897_; lean_object* v___x_2898_; lean_object* v_fst_2899_; lean_object* v_snd_2900_; lean_object* v___x_2901_; lean_object* v_cache_2902_; lean_object* v_zetaDeltaFVarIds_2903_; lean_object* v_postponed_2904_; lean_object* v_diag_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2914_; 
v___x_2896_ = lean_st_ref_get(v___y_2892_);
v_mctx_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc_ref(v_mctx_2897_);
lean_dec(v___x_2896_);
v___x_2898_ = l_Lean_instantiateMVarsCore(v_mctx_2897_, v_e_2891_);
v_fst_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_fst_2899_);
v_snd_2900_ = lean_ctor_get(v___x_2898_, 1);
lean_inc(v_snd_2900_);
lean_dec_ref(v___x_2898_);
v___x_2901_ = lean_st_ref_take(v___y_2892_);
v_cache_2902_ = lean_ctor_get(v___x_2901_, 1);
v_zetaDeltaFVarIds_2903_ = lean_ctor_get(v___x_2901_, 2);
v_postponed_2904_ = lean_ctor_get(v___x_2901_, 3);
v_diag_2905_ = lean_ctor_get(v___x_2901_, 4);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v___x_2901_, 0);
lean_dec(v_unused_2915_);
v___x_2907_ = v___x_2901_;
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_diag_2905_);
lean_inc(v_postponed_2904_);
lean_inc(v_zetaDeltaFVarIds_2903_);
lean_inc(v_cache_2902_);
lean_dec(v___x_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v_snd_2900_);
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_snd_2900_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_cache_2902_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_zetaDeltaFVarIds_2903_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_postponed_2904_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_diag_2905_);
v___x_2910_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_st_ref_set(v___y_2892_, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_fst_2899_);
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2916_, v___y_2917_);
lean_dec(v___y_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2920_, v___y_2924_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2937_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_24910__overap_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_24910__overap_2948_ = lean_panic_fn_borrowed(v___x_2947_, v_msg_2939_);
lean_inc(v___y_2945_);
lean_inc_ref(v___y_2944_);
lean_inc(v___y_2943_);
lean_inc_ref(v___y_2942_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
v___x_2949_ = lean_apply_7(v___x_24910__overap_2948_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, lean_box(0));
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object* v_a_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object* v_a_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_00_u03b1_2977_, lean_object* v_a_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_a_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_00_u03b1_2987_, v_a_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object* v_k_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v_b_3000_, lean_object* v_c_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v___x_3007_; 
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
v___x_3007_ = lean_apply_9(v_k_2997_, v_b_3000_, v_c_3001_, v___y_2998_, v___y_2999_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, lean_box(0));
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object* v_k_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v_b_3011_, lean_object* v_c_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_3008_, v___y_3009_, v___y_3010_, v_b_3011_, v_c_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_type_3019_, lean_object* v_k_3020_, uint8_t v_cleanupAnnotations_3021_, uint8_t v_whnfType_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___f_3030_; lean_object* v___x_3031_; 
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3023_);
v___f_3030_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3030_, 0, v_k_3020_);
lean_closure_set(v___f_3030_, 1, v___y_3023_);
lean_closure_set(v___f_3030_, 2, v___y_3024_);
v___x_3031_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3019_, v___f_3030_, v_cleanupAnnotations_3021_, v_whnfType_3022_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
if (lean_obj_tag(v___x_3031_) == 0)
{
return v___x_3031_;
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_type_3040_, lean_object* v_k_3041_, lean_object* v_cleanupAnnotations_3042_, lean_object* v_whnfType_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3051_; uint8_t v_whnfType_boxed_3052_; lean_object* v_res_3053_; 
v_cleanupAnnotations_boxed_3051_ = lean_unbox(v_cleanupAnnotations_3042_);
v_whnfType_boxed_3052_ = lean_unbox(v_whnfType_3043_);
v_res_3053_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3040_, v_k_3041_, v_cleanupAnnotations_boxed_3051_, v_whnfType_boxed_3052_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_3054_, lean_object* v_type_3055_, lean_object* v_k_3056_, uint8_t v_cleanupAnnotations_3057_, uint8_t v_whnfType_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3055_, v_k_3056_, v_cleanupAnnotations_3057_, v_whnfType_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_3067_, lean_object* v_type_3068_, lean_object* v_k_3069_, lean_object* v_cleanupAnnotations_3070_, lean_object* v_whnfType_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3079_; uint8_t v_whnfType_boxed_3080_; lean_object* v_res_3081_; 
v_cleanupAnnotations_boxed_3079_ = lean_unbox(v_cleanupAnnotations_3070_);
v_whnfType_boxed_3080_ = lean_unbox(v_whnfType_3071_);
v_res_3081_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_3067_, v_type_3068_, v_k_3069_, v_cleanupAnnotations_boxed_3079_, v_whnfType_boxed_3080_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
return v_res_3081_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3084_ = l_Lean_stringToMessageData(v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec_ref(v_x_3095_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v___x_3104_, lean_object* v_fst_3105_, lean_object* v_____r_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = l_Lean_mkAppN(v___x_3104_, v_fst_3105_);
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v___x_3116_, lean_object* v_fst_3117_, lean_object* v_____r_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3116_, v_fst_3117_, v_____r_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec_ref(v_fst_3117_);
return v_res_3126_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0));
v___x_3129_ = l_Lean_stringToMessageData(v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v_ctorName_3130_, uint8_t v___x_3131_, lean_object* v_x_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3140_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1);
v___x_3141_ = l_Lean_MessageData_ofConstName(v_ctorName_3130_, v___x_3131_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v_ctorName_3146_, lean_object* v___x_3147_, lean_object* v_x_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
uint8_t v___x_29822__boxed_3156_; lean_object* v_res_3157_; 
v___x_29822__boxed_3156_ = lean_unbox(v___x_3147_);
v_res_3157_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3146_, v___x_29822__boxed_3156_, v_x_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec_ref(v_x_3148_);
return v_res_3157_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object* v_e_3158_){
_start:
{
if (lean_obj_tag(v_e_3158_) == 0)
{
uint8_t v___x_3159_; 
v___x_3159_ = 2;
return v___x_3159_;
}
else
{
uint8_t v___x_3160_; 
v___x_3160_ = 0;
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object* v_e_3161_){
_start:
{
uint8_t v_res_3162_; lean_object* v_r_3163_; 
v_res_3162_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3161_);
lean_dec_ref(v_e_3161_);
v_r_3163_ = lean_box(v_res_3162_);
return v_r_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v_cls_3164_, uint8_t v_collapsed_3165_, lean_object* v_tag_3166_, lean_object* v_opts_3167_, uint8_t v_clsEnabled_3168_, lean_object* v_oldTraces_3169_, lean_object* v_msg_3170_, lean_object* v_resStartStop_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_fst_3179_; lean_object* v_snd_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3278_; 
v_fst_3179_ = lean_ctor_get(v_resStartStop_3171_, 0);
v_snd_3180_ = lean_ctor_get(v_resStartStop_3171_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_resStartStop_3171_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3182_ = v_resStartStop_3171_;
v_isShared_3183_ = v_isSharedCheck_3278_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_snd_3180_);
lean_inc(v_fst_3179_);
lean_dec(v_resStartStop_3171_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3278_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v_data_3187_; lean_object* v_fst_3198_; lean_object* v_snd_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3277_; 
v_fst_3198_ = lean_ctor_get(v_snd_3180_, 0);
v_snd_3199_ = lean_ctor_get(v_snd_3180_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_snd_3180_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3201_ = v_snd_3180_;
v_isShared_3202_ = v_isSharedCheck_3277_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_snd_3199_);
lean_inc(v_fst_3198_);
lean_dec(v_snd_3180_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3277_;
goto v_resetjp_3200_;
}
v___jp_3184_:
{
lean_object* v___x_3188_; 
lean_inc(v___y_3185_);
v___x_3188_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_oldTraces_3169_, v_data_3187_, v___y_3185_, v___y_3186_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref(v___x_3188_);
v___x_3189_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(v_fst_3179_);
return v___x_3189_;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_fst_3179_);
v_a_3190_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3188_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3188_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; uint8_t v___x_3204_; lean_object* v___y_3206_; lean_object* v_a_3207_; uint8_t v___y_3231_; double v___y_3262_; 
v___x_3203_ = l_Lean_trace_profiler;
v___x_3204_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3167_, v___x_3203_);
if (v___x_3204_ == 0)
{
v___y_3231_ = v___x_3204_;
goto v___jp_3230_;
}
else
{
lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3267_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3268_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3167_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; double v___x_3271_; double v___x_3272_; double v___x_3273_; 
v___x_3269_ = l_Lean_trace_profiler_threshold;
v___x_3270_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3167_, v___x_3269_);
v___x_3271_ = lean_float_of_nat(v___x_3270_);
v___x_3272_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__4);
v___x_3273_ = lean_float_div(v___x_3271_, v___x_3272_);
v___y_3262_ = v___x_3273_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; double v___x_3276_; 
v___x_3274_ = l_Lean_trace_profiler_threshold;
v___x_3275_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3167_, v___x_3274_);
v___x_3276_ = lean_float_of_nat(v___x_3275_);
v___y_3262_ = v___x_3276_;
goto v___jp_3261_;
}
}
v___jp_3205_:
{
uint8_t v_result_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v_result_3208_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_fst_3179_);
v___x_3209_ = l_Lean_TraceResult_toEmoji(v_result_3208_);
v___x_3210_ = l_Lean_stringToMessageData(v___x_3209_);
v___x_3211_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
if (v_isShared_3202_ == 0)
{
lean_ctor_set_tag(v___x_3201_, 7);
lean_ctor_set(v___x_3201_, 1, v___x_3211_);
lean_ctor_set(v___x_3201_, 0, v___x_3210_);
v___x_3213_ = v___x_3201_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v_m_3215_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set_tag(v___x_3182_, 7);
lean_ctor_set(v___x_3182_, 1, v_a_3207_);
lean_ctor_set(v___x_3182_, 0, v___x_3213_);
v_m_3215_ = v___x_3182_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_a_3207_);
v_m_3215_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; double v___x_3218_; lean_object* v_data_3219_; 
v___x_3216_ = lean_box(v_result_3208_);
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
v___x_3218_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3166_);
lean_inc_ref(v___x_3217_);
lean_inc(v_cls_3164_);
v_data_3219_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3219_, 0, v_cls_3164_);
lean_ctor_set(v_data_3219_, 1, v___x_3217_);
lean_ctor_set(v_data_3219_, 2, v_tag_3166_);
lean_ctor_set_float(v_data_3219_, sizeof(void*)*3, v___x_3218_);
lean_ctor_set_float(v_data_3219_, sizeof(void*)*3 + 8, v___x_3218_);
lean_ctor_set_uint8(v_data_3219_, sizeof(void*)*3 + 16, v_collapsed_3165_);
if (v___x_3204_ == 0)
{
lean_dec_ref(v___x_3217_);
lean_dec(v_snd_3199_);
lean_dec(v_fst_3198_);
lean_dec_ref(v_tag_3166_);
lean_dec(v_cls_3164_);
v___y_3185_ = v___y_3206_;
v___y_3186_ = v_m_3215_;
v_data_3187_ = v_data_3219_;
goto v___jp_3184_;
}
else
{
lean_object* v_data_3220_; double v___x_3221_; double v___x_3222_; 
lean_dec_ref(v_data_3219_);
v_data_3220_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3220_, 0, v_cls_3164_);
lean_ctor_set(v_data_3220_, 1, v___x_3217_);
lean_ctor_set(v_data_3220_, 2, v_tag_3166_);
v___x_3221_ = lean_unbox_float(v_fst_3198_);
lean_dec(v_fst_3198_);
lean_ctor_set_float(v_data_3220_, sizeof(void*)*3, v___x_3221_);
v___x_3222_ = lean_unbox_float(v_snd_3199_);
lean_dec(v_snd_3199_);
lean_ctor_set_float(v_data_3220_, sizeof(void*)*3 + 8, v___x_3222_);
lean_ctor_set_uint8(v_data_3220_, sizeof(void*)*3 + 16, v_collapsed_3165_);
v___y_3185_ = v___y_3206_;
v___y_3186_ = v_m_3215_;
v_data_3187_ = v_data_3220_;
goto v___jp_3184_;
}
}
}
}
v___jp_3225_:
{
lean_object* v_ref_3226_; lean_object* v___x_3227_; 
v_ref_3226_ = lean_ctor_get(v___y_3176_, 5);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
lean_inc(v___y_3175_);
lean_inc_ref(v___y_3174_);
lean_inc(v___y_3173_);
lean_inc_ref(v___y_3172_);
lean_inc(v_fst_3179_);
v___x_3227_ = lean_apply_8(v_msg_3170_, v_fst_3179_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, lean_box(0));
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref(v___x_3227_);
v___y_3206_ = v_ref_3226_;
v_a_3207_ = v_a_3228_;
goto v___jp_3205_;
}
else
{
lean_object* v___x_3229_; 
lean_dec_ref(v___x_3227_);
v___x_3229_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__3);
v___y_3206_ = v_ref_3226_;
v_a_3207_ = v___x_3229_;
goto v___jp_3205_;
}
}
v___jp_3230_:
{
if (v_clsEnabled_3168_ == 0)
{
if (v___y_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v_traceState_3233_; lean_object* v_env_3234_; lean_object* v_nextMacroScope_3235_; lean_object* v_ngen_3236_; lean_object* v_auxDeclNGen_3237_; lean_object* v_cache_3238_; lean_object* v_messages_3239_; lean_object* v_infoState_3240_; lean_object* v_snapshotTasks_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3260_; 
lean_del_object(v___x_3201_);
lean_dec(v_snd_3199_);
lean_dec(v_fst_3198_);
lean_del_object(v___x_3182_);
lean_dec_ref(v_msg_3170_);
lean_dec_ref(v_tag_3166_);
lean_dec(v_cls_3164_);
v___x_3232_ = lean_st_ref_take(v___y_3177_);
v_traceState_3233_ = lean_ctor_get(v___x_3232_, 4);
v_env_3234_ = lean_ctor_get(v___x_3232_, 0);
v_nextMacroScope_3235_ = lean_ctor_get(v___x_3232_, 1);
v_ngen_3236_ = lean_ctor_get(v___x_3232_, 2);
v_auxDeclNGen_3237_ = lean_ctor_get(v___x_3232_, 3);
v_cache_3238_ = lean_ctor_get(v___x_3232_, 5);
v_messages_3239_ = lean_ctor_get(v___x_3232_, 6);
v_infoState_3240_ = lean_ctor_get(v___x_3232_, 7);
v_snapshotTasks_3241_ = lean_ctor_get(v___x_3232_, 8);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3243_ = v___x_3232_;
v_isShared_3244_ = v_isSharedCheck_3260_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_snapshotTasks_3241_);
lean_inc(v_infoState_3240_);
lean_inc(v_messages_3239_);
lean_inc(v_cache_3238_);
lean_inc(v_traceState_3233_);
lean_inc(v_auxDeclNGen_3237_);
lean_inc(v_ngen_3236_);
lean_inc(v_nextMacroScope_3235_);
lean_inc(v_env_3234_);
lean_dec(v___x_3232_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3260_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
uint64_t v_tid_3245_; lean_object* v_traces_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3259_; 
v_tid_3245_ = lean_ctor_get_uint64(v_traceState_3233_, sizeof(void*)*1);
v_traces_3246_ = lean_ctor_get(v_traceState_3233_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_traceState_3233_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3248_ = v_traceState_3233_;
v_isShared_3249_ = v_isSharedCheck_3259_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_traces_3246_);
lean_dec(v_traceState_3233_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3259_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3250_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3169_, v_traces_3246_);
lean_dec_ref(v_traces_3246_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v___x_3250_);
v___x_3252_ = v___x_3248_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3250_);
lean_ctor_set_uint64(v_reuseFailAlloc_3258_, sizeof(void*)*1, v_tid_3245_);
v___x_3252_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 4, v___x_3252_);
v___x_3254_ = v___x_3243_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_env_3234_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_nextMacroScope_3235_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_ngen_3236_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_auxDeclNGen_3237_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3257_, 5, v_cache_3238_);
lean_ctor_set(v_reuseFailAlloc_3257_, 6, v_messages_3239_);
lean_ctor_set(v_reuseFailAlloc_3257_, 7, v_infoState_3240_);
lean_ctor_set(v_reuseFailAlloc_3257_, 8, v_snapshotTasks_3241_);
v___x_3254_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_st_ref_set(v___y_3177_, v___x_3254_);
v___x_3256_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___redArg(v_fst_3179_);
return v___x_3256_;
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
v___jp_3261_:
{
double v___x_3263_; double v___x_3264_; double v___x_3265_; uint8_t v___x_3266_; 
v___x_3263_ = lean_unbox_float(v_snd_3199_);
v___x_3264_ = lean_unbox_float(v_fst_3198_);
v___x_3265_ = lean_float_sub(v___x_3263_, v___x_3264_);
v___x_3266_ = lean_float_decLt(v___y_3262_, v___x_3265_);
v___y_3231_ = v___x_3266_;
goto v___jp_3230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v_cls_3279_, lean_object* v_collapsed_3280_, lean_object* v_tag_3281_, lean_object* v_opts_3282_, lean_object* v_clsEnabled_3283_, lean_object* v_oldTraces_3284_, lean_object* v_msg_3285_, lean_object* v_resStartStop_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v_collapsed_boxed_3294_; uint8_t v_clsEnabled_boxed_3295_; lean_object* v_res_3296_; 
v_collapsed_boxed_3294_ = lean_unbox(v_collapsed_3280_);
v_clsEnabled_boxed_3295_ = lean_unbox(v_clsEnabled_3283_);
v_res_3296_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3279_, v_collapsed_boxed_3294_, v_tag_3281_, v_opts_3282_, v_clsEnabled_boxed_3295_, v_oldTraces_3284_, v_msg_3285_, v_resStartStop_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec_ref(v_opts_3282_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v___x_3297_, lean_object* v_as_3298_, size_t v_i_3299_, size_t v_stop_3300_, lean_object* v_b_3301_){
_start:
{
lean_object* v___y_3303_; uint8_t v___x_3307_; 
v___x_3307_ = lean_usize_dec_eq(v_i_3299_, v_stop_3300_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = lean_array_uget_borrowed(v_as_3298_, v_i_3299_);
v___x_3309_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v___x_3297_, v___x_3308_);
if (v___x_3309_ == 0)
{
v___y_3303_ = v_b_3301_;
goto v___jp_3302_;
}
else
{
lean_object* v___x_3310_; 
lean_inc(v___x_3308_);
v___x_3310_ = lean_array_push(v_b_3301_, v___x_3308_);
v___y_3303_ = v___x_3310_;
goto v___jp_3302_;
}
}
else
{
return v_b_3301_;
}
v___jp_3302_:
{
size_t v___x_3304_; size_t v___x_3305_; 
v___x_3304_ = ((size_t)1ULL);
v___x_3305_ = lean_usize_add(v_i_3299_, v___x_3304_);
v_i_3299_ = v___x_3305_;
v_b_3301_ = v___y_3303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v___x_3311_, lean_object* v_as_3312_, lean_object* v_i_3313_, lean_object* v_stop_3314_, lean_object* v_b_3315_){
_start:
{
size_t v_i_boxed_3316_; size_t v_stop_boxed_3317_; lean_object* v_res_3318_; 
v_i_boxed_3316_ = lean_unbox_usize(v_i_3313_);
lean_dec(v_i_3313_);
v_stop_boxed_3317_ = lean_unbox_usize(v_stop_3314_);
lean_dec(v_stop_3314_);
v_res_3318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3311_, v_as_3312_, v_i_boxed_3316_, v_stop_boxed_3317_, v_b_3315_);
lean_dec_ref(v_as_3312_);
lean_dec_ref(v___x_3311_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
if (lean_obj_tag(v_a_3319_) == 0)
{
lean_object* v___x_3321_; 
v___x_3321_ = l_List_reverse___redArg(v_a_3320_);
return v___x_3321_;
}
else
{
lean_object* v_head_3322_; lean_object* v_tail_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3332_; 
v_head_3322_ = lean_ctor_get(v_a_3319_, 0);
v_tail_3323_ = lean_ctor_get(v_a_3319_, 1);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_a_3319_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3325_ = v_a_3319_;
v_isShared_3326_ = v_isSharedCheck_3332_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_tail_3323_);
lean_inc(v_head_3322_);
lean_dec(v_a_3319_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3332_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3327_ = l_Lean_MessageData_ofExpr(v_head_3322_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 1, v_a_3320_);
lean_ctor_set(v___x_3325_, 0, v___x_3327_);
v___x_3329_ = v___x_3325_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_a_3320_);
v___x_3329_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
v_a_3319_ = v_tail_3323_;
v_a_3320_ = v___x_3329_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3337_ = lean_unsigned_to_nat(6u);
v___x_3338_ = lean_unsigned_to_nat(108u);
v___x_3339_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3341_ = l_mkPanicMessageWithDecl(v___x_3340_, v___x_3339_, v___x_3338_, v___x_3337_, v___x_3336_);
return v___x_3341_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3344_ = l_Lean_stringToMessageData(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3347_ = l_Lean_stringToMessageData(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3352_ = l_Lean_stringToMessageData(v___x_3351_);
return v___x_3352_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_box(0);
v___x_3354_ = lean_unsigned_to_nat(16u);
v___x_3355_ = lean_mk_array(v___x_3354_, v___x_3353_);
return v___x_3355_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12));
v___x_3358_ = l_Lean_stringToMessageData(v___x_3357_);
return v___x_3358_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14));
v___x_3361_ = l_Lean_stringToMessageData(v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16));
v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3372_, lean_object* v_us_3373_, lean_object* v_xs_3374_, lean_object* v___x_3375_, lean_object* v___x_3376_, lean_object* v_ctorName_3377_, lean_object* v___x_3378_, lean_object* v___f_3379_, lean_object* v_insts_3380_, lean_object* v_localInst2Index_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; lean_object* v_env_3390_; lean_object* v___x_3391_; lean_object* v_type_3392_; lean_object* v___y_3394_; uint8_t v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; uint8_t v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_val_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3561_; lean_object* v___y_3572_; uint8_t v___x_3582_; uint8_t v___x_3583_; 
v___x_3389_ = lean_st_ref_get(v___y_3387_);
v_env_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_ref(v_env_3390_);
lean_dec(v___x_3389_);
lean_inc(v_us_3373_);
lean_inc(v_inductiveTypeName_3372_);
v___x_3391_ = l_Lean_Expr_const___override(v_inductiveTypeName_3372_, v_us_3373_);
v_type_3392_ = l_Lean_mkAppN(v___x_3391_, v_xs_3374_);
v___x_3582_ = l_Lean_isStructure(v_env_3390_, v_inductiveTypeName_3372_);
v___x_3583_ = 1;
if (v___x_3582_ == 0)
{
lean_object* v_options_3584_; lean_object* v_inheritedTraceOptions_3585_; uint8_t v_hasTrace_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec_ref(v___f_3379_);
v_options_3584_ = lean_ctor_get(v___y_3386_, 2);
v_inheritedTraceOptions_3585_ = lean_ctor_get(v___y_3386_, 13);
v_hasTrace_3586_ = lean_ctor_get_uint8(v_options_3584_, sizeof(void*)*1);
lean_inc(v_ctorName_3377_);
v___x_3587_ = l_Lean_Expr_const___override(v_ctorName_3377_, v_us_3373_);
v___x_3588_ = l_Lean_mkAppN(v___x_3587_, v___x_3378_);
if (v_hasTrace_3586_ == 0)
{
lean_object* v___x_3589_; 
lean_dec(v_ctorName_3377_);
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3386_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc_ref(v___x_3588_);
v___x_3589_ = lean_infer_type(v___x_3588_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; lean_object* v___x_3593_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref(v___x_3589_);
v___x_3591_ = lean_box(0);
v___x_3592_ = 0;
v___x_3593_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3590_, v___x_3591_, v___x_3592_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v_snd_3595_; lean_object* v_fst_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3639_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v_snd_3595_ = lean_ctor_get(v_a_3594_, 1);
v_fst_3596_ = lean_ctor_get(v_a_3594_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v_a_3594_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3598_ = v_a_3594_;
v_isShared_3599_ = v_isSharedCheck_3639_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_snd_3595_);
lean_inc(v_fst_3596_);
lean_dec(v_a_3594_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3639_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v_snd_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3637_; 
v_snd_3600_ = lean_ctor_get(v_snd_3595_, 1);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_snd_3595_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v_snd_3595_, 0);
lean_dec(v_unused_3638_);
v___x_3602_ = v_snd_3595_;
v_isShared_3603_ = v_isSharedCheck_3637_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_snd_3600_);
lean_dec(v_snd_3595_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3637_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; 
lean_inc(v_snd_3600_);
lean_inc_ref(v_type_3392_);
v___x_3604_ = l_Lean_Meta_isExprDefEq(v_type_3392_, v_snd_3600_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; uint8_t v___x_3606_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___x_3604_);
v___x_3606_ = lean_unbox(v_a_3605_);
lean_dec(v_a_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
lean_dec(v_fst_3596_);
lean_dec_ref(v___x_3588_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v___x_3607_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3608_ = l_Lean_indentExpr(v_type_3392_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 7);
lean_ctor_set(v___x_3602_, 1, v___x_3608_);
lean_ctor_set(v___x_3602_, 0, v___x_3607_);
v___x_3610_ = v___x_3602_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3599_ == 0)
{
lean_ctor_set_tag(v___x_3598_, 7);
lean_ctor_set(v___x_3598_, 1, v___x_3611_);
lean_ctor_set(v___x_3598_, 0, v___x_3610_);
v___x_3613_ = v___x_3598_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v___x_3614_ = l_Lean_indentExpr(v_snd_3600_);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3615_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
else
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_del_object(v___x_3602_);
lean_dec(v_snd_3600_);
lean_del_object(v___x_3598_);
v___x_3627_ = lean_box(0);
v___x_3628_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3588_, v_fst_3596_, v___x_3627_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v_fst_3596_);
v___y_3561_ = v___x_3628_;
goto v___jp_3560_;
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_del_object(v___x_3602_);
lean_dec(v_snd_3600_);
lean_del_object(v___x_3598_);
lean_dec(v_fst_3596_);
lean_dec_ref(v___x_3588_);
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v_a_3629_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3604_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3604_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v___x_3588_);
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v_a_3640_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3593_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3593_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_dec_ref(v___x_3588_);
v___y_3561_ = v___x_3589_;
goto v___jp_3560_;
}
}
else
{
lean_object* v___x_3648_; lean_object* v___f_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v_a_3657_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v_a_3672_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v_a_3690_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v_a_3702_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; 
v___x_3648_ = lean_box(v___x_3582_);
v___f_3649_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3649_, 0, v_ctorName_3377_);
lean_closure_set(v___f_3649_, 1, v___x_3648_);
v___x_3650_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3651_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3652_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3653_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3585_, v_options_3584_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3800_ = l_Lean_trace_profiler;
v___x_3801_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3584_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; 
lean_dec_ref(v___f_3649_);
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3386_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc_ref(v___x_3588_);
v___x_3802_ = lean_infer_type(v___x_3588_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; lean_object* v___x_3806_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref(v___x_3802_);
v___x_3804_ = lean_box(0);
v___x_3805_ = 0;
v___x_3806_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3803_, v___x_3804_, v___x_3805_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v_snd_3808_; lean_object* v_fst_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3852_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3806_);
v_snd_3808_ = lean_ctor_get(v_a_3807_, 1);
v_fst_3809_ = lean_ctor_get(v_a_3807_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_a_3807_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3811_ = v_a_3807_;
v_isShared_3812_ = v_isSharedCheck_3852_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_snd_3808_);
lean_inc(v_fst_3809_);
lean_dec(v_a_3807_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3852_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v_snd_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3850_; 
v_snd_3813_ = lean_ctor_get(v_snd_3808_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_snd_3808_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v_snd_3808_, 0);
lean_dec(v_unused_3851_);
v___x_3815_ = v_snd_3808_;
v_isShared_3816_ = v_isSharedCheck_3850_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_snd_3813_);
lean_dec(v_snd_3808_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3850_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; 
lean_inc(v_snd_3813_);
lean_inc_ref(v_type_3392_);
v___x_3817_ = l_Lean_Meta_isExprDefEq(v_type_3392_, v_snd_3813_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; uint8_t v___x_3819_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3817_);
v___x_3819_ = lean_unbox(v_a_3818_);
lean_dec(v_a_3818_);
if (v___x_3819_ == 0)
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
lean_dec(v_fst_3809_);
lean_dec_ref(v___x_3588_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v___x_3820_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3821_ = l_Lean_indentExpr(v_type_3392_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set_tag(v___x_3815_, 7);
lean_ctor_set(v___x_3815_, 1, v___x_3821_);
lean_ctor_set(v___x_3815_, 0, v___x_3820_);
v___x_3823_ = v___x_3815_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3824_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3812_ == 0)
{
lean_ctor_set_tag(v___x_3811_, 7);
lean_ctor_set(v___x_3811_, 1, v___x_3824_);
lean_ctor_set(v___x_3811_, 0, v___x_3823_);
v___x_3826_ = v___x_3811_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
v___x_3827_ = l_Lean_indentExpr(v_snd_3813_);
v___x_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3828_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
}
else
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_del_object(v___x_3815_);
lean_dec(v_snd_3813_);
lean_del_object(v___x_3811_);
v___x_3840_ = lean_box(0);
v___x_3841_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3588_, v_fst_3809_, v___x_3840_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v_fst_3809_);
v___y_3561_ = v___x_3841_;
goto v___jp_3560_;
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_del_object(v___x_3815_);
lean_dec(v_snd_3813_);
lean_del_object(v___x_3811_);
lean_dec(v_fst_3809_);
lean_dec_ref(v___x_3588_);
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v_a_3842_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3817_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3817_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec_ref(v___x_3588_);
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v_a_3853_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3806_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3806_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_dec_ref(v___x_3588_);
v___y_3561_ = v___x_3802_;
goto v___jp_3560_;
}
}
else
{
goto v___jp_3717_;
}
}
else
{
goto v___jp_3717_;
}
v___jp_3654_:
{
lean_object* v___x_3658_; double v___x_3659_; double v___x_3660_; double v___x_3661_; double v___x_3662_; double v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3658_ = lean_io_mono_nanos_now();
v___x_3659_ = lean_float_of_nat(v___y_3655_);
v___x_3660_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3661_ = lean_float_div(v___x_3659_, v___x_3660_);
v___x_3662_ = lean_float_of_nat(v___x_3658_);
v___x_3663_ = lean_float_div(v___x_3662_, v___x_3660_);
v___x_3664_ = lean_box_float(v___x_3661_);
v___x_3665_ = lean_box_float(v___x_3663_);
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v_a_3657_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3650_, v___x_3583_, v___x_3651_, v_options_3584_, v___x_3653_, v___y_3656_, v___f_3649_, v___x_3667_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v___y_3561_ = v___x_3668_;
goto v___jp_3560_;
}
v___jp_3669_:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_a_3672_);
v___y_3655_ = v___y_3670_;
v___y_3656_ = v___y_3671_;
v_a_3657_ = v___x_3673_;
goto v___jp_3654_;
}
v___jp_3674_:
{
if (lean_obj_tag(v___y_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
v_a_3678_ = lean_ctor_get(v___y_3677_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___y_3677_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___y_3677_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___y_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 1);
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
v___y_3655_ = v___y_3675_;
v___y_3656_ = v___y_3676_;
v_a_3657_ = v___x_3683_;
goto v___jp_3654_;
}
}
}
else
{
lean_object* v_a_3686_; 
v_a_3686_ = lean_ctor_get(v___y_3677_, 0);
lean_inc(v_a_3686_);
lean_dec_ref(v___y_3677_);
v___y_3670_ = v___y_3675_;
v___y_3671_ = v___y_3676_;
v_a_3672_ = v_a_3686_;
goto v___jp_3669_;
}
}
v___jp_3687_:
{
lean_object* v___x_3691_; double v___x_3692_; double v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3691_ = lean_io_get_num_heartbeats();
v___x_3692_ = lean_float_of_nat(v___y_3688_);
v___x_3693_ = lean_float_of_nat(v___x_3691_);
v___x_3694_ = lean_box_float(v___x_3692_);
v___x_3695_ = lean_box_float(v___x_3693_);
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_a_3690_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3650_, v___x_3583_, v___x_3651_, v_options_3584_, v___x_3653_, v___y_3689_, v___f_3649_, v___x_3697_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v___y_3561_ = v___x_3698_;
goto v___jp_3560_;
}
v___jp_3699_:
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_a_3702_);
v___y_3688_ = v___y_3700_;
v___y_3689_ = v___y_3701_;
v_a_3690_ = v___x_3703_;
goto v___jp_3687_;
}
v___jp_3704_:
{
if (lean_obj_tag(v___y_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
v_a_3708_ = lean_ctor_get(v___y_3707_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___y_3707_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___y_3707_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___y_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set_tag(v___x_3710_, 1);
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
v___y_3688_ = v___y_3705_;
v___y_3689_ = v___y_3706_;
v_a_3690_ = v___x_3713_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_3716_; 
v_a_3716_ = lean_ctor_get(v___y_3707_, 0);
lean_inc(v_a_3716_);
lean_dec_ref(v___y_3707_);
v___y_3700_ = v___y_3705_;
v___y_3701_ = v___y_3706_;
v_a_3702_ = v_a_3716_;
goto v___jp_3699_;
}
}
v___jp_3717_:
{
lean_object* v___x_3718_; lean_object* v_a_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3718_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3387_);
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref(v___x_3718_);
v___x_3720_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3721_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3584_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_io_mono_nanos_now();
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3386_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc_ref(v___x_3588_);
v___x_3723_ = lean_infer_type(v___x_3588_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref(v___x_3723_);
v___x_3725_ = lean_box(0);
v___x_3726_ = 0;
v___x_3727_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3724_, v___x_3725_, v___x_3726_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v_snd_3729_; lean_object* v_fst_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3759_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v_snd_3729_ = lean_ctor_get(v_a_3728_, 1);
v_fst_3730_ = lean_ctor_get(v_a_3728_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3728_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3732_ = v_a_3728_;
v_isShared_3733_ = v_isSharedCheck_3759_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_snd_3729_);
lean_inc(v_fst_3730_);
lean_dec(v_a_3728_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3759_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v_snd_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3757_; 
v_snd_3734_ = lean_ctor_get(v_snd_3729_, 1);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_snd_3729_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; 
v_unused_3758_ = lean_ctor_get(v_snd_3729_, 0);
lean_dec(v_unused_3758_);
v___x_3736_ = v_snd_3729_;
v_isShared_3737_ = v_isSharedCheck_3757_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_snd_3734_);
lean_dec(v_snd_3729_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3757_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; 
lean_inc(v_snd_3734_);
lean_inc_ref(v_type_3392_);
v___x_3738_ = l_Lean_Meta_isExprDefEq(v_type_3392_, v_snd_3734_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; uint8_t v___x_3740_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref(v___x_3738_);
v___x_3740_ = lean_unbox(v_a_3739_);
lean_dec(v_a_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
lean_dec(v_fst_3730_);
lean_dec_ref(v___x_3588_);
v___x_3741_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3392_);
v___x_3742_ = l_Lean_indentExpr(v_type_3392_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 7);
lean_ctor_set(v___x_3736_, 1, v___x_3742_);
lean_ctor_set(v___x_3736_, 0, v___x_3741_);
v___x_3744_ = v___x_3736_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3745_; lean_object* v___x_3747_; 
v___x_3745_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3733_ == 0)
{
lean_ctor_set_tag(v___x_3732_, 7);
lean_ctor_set(v___x_3732_, 1, v___x_3745_);
lean_ctor_set(v___x_3732_, 0, v___x_3744_);
v___x_3747_ = v___x_3732_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v_a_3751_; 
v___x_3748_ = l_Lean_indentExpr(v_snd_3734_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3749_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref(v___x_3750_);
v___y_3670_ = v___x_3722_;
v___y_3671_ = v_a_3719_;
v_a_3672_ = v_a_3751_;
goto v___jp_3669_;
}
}
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
lean_del_object(v___x_3736_);
lean_dec(v_snd_3734_);
lean_del_object(v___x_3732_);
v___x_3754_ = lean_box(0);
v___x_3755_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3588_, v_fst_3730_, v___x_3754_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v_fst_3730_);
v___y_3675_ = v___x_3722_;
v___y_3676_ = v_a_3719_;
v___y_3677_ = v___x_3755_;
goto v___jp_3674_;
}
}
else
{
lean_object* v_a_3756_; 
lean_del_object(v___x_3736_);
lean_dec(v_snd_3734_);
lean_del_object(v___x_3732_);
lean_dec(v_fst_3730_);
lean_dec_ref(v___x_3588_);
v_a_3756_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___x_3738_);
v___y_3670_ = v___x_3722_;
v___y_3671_ = v_a_3719_;
v_a_3672_ = v_a_3756_;
goto v___jp_3669_;
}
}
}
}
else
{
lean_object* v_a_3760_; 
lean_dec_ref(v___x_3588_);
v_a_3760_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3760_);
lean_dec_ref(v___x_3727_);
v___y_3670_ = v___x_3722_;
v___y_3671_ = v_a_3719_;
v_a_3672_ = v_a_3760_;
goto v___jp_3669_;
}
}
else
{
lean_dec_ref(v___x_3588_);
v___y_3675_ = v___x_3722_;
v___y_3676_ = v_a_3719_;
v___y_3677_ = v___x_3723_;
goto v___jp_3674_;
}
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3386_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc_ref(v___x_3588_);
v___x_3762_ = lean_infer_type(v___x_3588_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = lean_box(0);
v___x_3765_ = 0;
v___x_3766_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3763_, v___x_3764_, v___x_3765_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v_snd_3768_; lean_object* v_fst_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3798_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref(v___x_3766_);
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
lean_inc_ref(v_type_3392_);
v___x_3777_ = l_Lean_Meta_isExprDefEq(v_type_3392_, v_snd_3773_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; uint8_t v___x_3779_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref(v___x_3777_);
v___x_3779_ = lean_unbox(v_a_3778_);
lean_dec(v_a_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
lean_dec(v_fst_3769_);
lean_dec_ref(v___x_3588_);
v___x_3780_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3392_);
v___x_3781_ = l_Lean_indentExpr(v_type_3392_);
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
v___x_3789_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3788_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___y_3700_ = v___x_3761_;
v___y_3701_ = v_a_3719_;
v_a_3702_ = v_a_3790_;
goto v___jp_3699_;
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
v___x_3794_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3588_, v_fst_3769_, v___x_3793_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v_fst_3769_);
v___y_3705_ = v___x_3761_;
v___y_3706_ = v_a_3719_;
v___y_3707_ = v___x_3794_;
goto v___jp_3704_;
}
}
else
{
lean_object* v_a_3795_; 
lean_del_object(v___x_3775_);
lean_dec(v_snd_3773_);
lean_del_object(v___x_3771_);
lean_dec(v_fst_3769_);
lean_dec_ref(v___x_3588_);
v_a_3795_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3777_);
v___y_3700_ = v___x_3761_;
v___y_3701_ = v_a_3719_;
v_a_3702_ = v_a_3795_;
goto v___jp_3699_;
}
}
}
}
else
{
lean_object* v_a_3799_; 
lean_dec_ref(v___x_3588_);
v_a_3799_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3799_);
lean_dec_ref(v___x_3766_);
v___y_3700_ = v___x_3761_;
v___y_3701_ = v_a_3719_;
v_a_3702_ = v_a_3799_;
goto v___jp_3699_;
}
}
else
{
lean_dec_ref(v___x_3588_);
v___y_3705_ = v___x_3761_;
v___y_3706_ = v_a_3719_;
v___y_3707_ = v___x_3762_;
goto v___jp_3704_;
}
}
}
}
}
else
{
lean_object* v_options_3861_; uint8_t v_hasTrace_3862_; 
lean_dec(v_ctorName_3377_);
lean_dec(v_us_3373_);
v_options_3861_ = lean_ctor_get(v___y_3386_, 2);
v_hasTrace_3862_ = lean_ctor_get_uint8(v_options_3861_, sizeof(void*)*1);
if (v_hasTrace_3862_ == 0)
{
lean_object* v_ref_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_dec_ref(v___f_3379_);
v_ref_3863_ = lean_ctor_get(v___y_3386_, 5);
v___x_3864_ = l_Lean_SourceInfo_fromRef(v_ref_3863_, v_hasTrace_3862_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3864_);
v___x_3867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3864_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = l_Lean_Syntax_node1(v___x_3864_, v___x_3865_, v___x_3867_);
lean_inc_ref(v_type_3392_);
v___x_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3869_, 0, v_type_3392_);
v___x_3870_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3870_, 0, v___x_3868_);
lean_closure_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3870_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v___y_3572_ = v___x_3871_;
goto v___jp_3571_;
}
else
{
lean_object* v_ref_3872_; lean_object* v_inheritedTraceOptions_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v_a_3881_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v_a_3896_; 
v_ref_3872_ = lean_ctor_get(v___y_3386_, 5);
v_inheritedTraceOptions_3873_ = lean_ctor_get(v___y_3386_, 13);
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3875_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3876_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3877_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3873_, v_options_3861_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3969_ = l_Lean_trace_profiler;
v___x_3970_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3861_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec_ref(v___f_3379_);
v___x_3971_ = l_Lean_SourceInfo_fromRef(v_ref_3872_, v___x_3970_);
v___x_3972_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3973_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3971_);
v___x_3974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3971_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = l_Lean_Syntax_node1(v___x_3971_, v___x_3972_, v___x_3974_);
lean_inc_ref(v_type_3392_);
v___x_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3976_, 0, v_type_3392_);
v___x_3977_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3977_, 0, v___x_3975_);
lean_closure_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3977_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v___y_3572_ = v___x_3978_;
goto v___jp_3571_;
}
else
{
goto v___jp_3905_;
}
}
else
{
goto v___jp_3905_;
}
v___jp_3878_:
{
lean_object* v___x_3882_; double v___x_3883_; double v___x_3884_; double v___x_3885_; double v___x_3886_; double v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3882_ = lean_io_mono_nanos_now();
v___x_3883_ = lean_float_of_nat(v___y_3880_);
v___x_3884_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3885_ = lean_float_div(v___x_3883_, v___x_3884_);
v___x_3886_ = lean_float_of_nat(v___x_3882_);
v___x_3887_ = lean_float_div(v___x_3886_, v___x_3884_);
v___x_3888_ = lean_box_float(v___x_3885_);
v___x_3889_ = lean_box_float(v___x_3887_);
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3891_, 0, v_a_3881_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3874_, v___x_3583_, v___x_3875_, v_options_3861_, v___x_3877_, v___y_3879_, v___f_3379_, v___x_3891_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v___y_3572_ = v___x_3892_;
goto v___jp_3571_;
}
v___jp_3893_:
{
lean_object* v___x_3897_; double v___x_3898_; double v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3897_ = lean_io_get_num_heartbeats();
v___x_3898_ = lean_float_of_nat(v___y_3895_);
v___x_3899_ = lean_float_of_nat(v___x_3897_);
v___x_3900_ = lean_box_float(v___x_3898_);
v___x_3901_ = lean_box_float(v___x_3899_);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v_a_3896_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3874_, v___x_3583_, v___x_3875_, v_options_3861_, v___x_3877_, v___y_3894_, v___f_3379_, v___x_3903_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v___y_3572_ = v___x_3904_;
goto v___jp_3571_;
}
v___jp_3905_:
{
lean_object* v___x_3906_; lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3968_; 
v___x_3906_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3387_);
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3968_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3968_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; uint8_t v___x_3912_; 
v___x_3911_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3912_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3861_, v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3913_ = lean_io_mono_nanos_now();
v___x_3914_ = l_Lean_SourceInfo_fromRef(v_ref_3872_, v___x_3912_);
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3916_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3914_);
v___x_3917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3914_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = l_Lean_Syntax_node1(v___x_3914_, v___x_3915_, v___x_3917_);
lean_inc_ref(v_type_3392_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set_tag(v___x_3909_, 1);
lean_ctor_set(v___x_3909_, 0, v_type_3392_);
v___x_3920_ = v___x_3909_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_type_3392_);
v___x_3920_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3921_, 0, v___x_3918_);
lean_closure_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3921_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
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
lean_ctor_set_tag(v___x_3925_, 1);
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
v___y_3879_ = v_a_3907_;
v___y_3880_ = v___x_3913_;
v_a_3881_ = v___x_3928_;
goto v___jp_3878_;
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
v_a_3931_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3922_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3922_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
lean_ctor_set_tag(v___x_3933_, 0);
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
v___y_3879_ = v_a_3907_;
v___y_3880_ = v___x_3913_;
v_a_3881_ = v___x_3936_;
goto v___jp_3878_;
}
}
}
}
}
else
{
lean_object* v___x_3940_; uint8_t v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3940_ = lean_io_get_num_heartbeats();
v___x_3941_ = 0;
v___x_3942_ = l_Lean_SourceInfo_fromRef(v_ref_3872_, v___x_3941_);
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3944_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3942_);
v___x_3945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3942_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = l_Lean_Syntax_node1(v___x_3942_, v___x_3943_, v___x_3945_);
lean_inc_ref(v_type_3392_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set_tag(v___x_3909_, 1);
lean_ctor_set(v___x_3909_, 0, v_type_3392_);
v___x_3948_ = v___x_3909_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_type_3392_);
v___x_3948_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3949_, 0, v___x_3946_);
lean_closure_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3949_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3950_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3950_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set_tag(v___x_3953_, 1);
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
v___y_3894_ = v_a_3907_;
v___y_3895_ = v___x_3940_;
v_a_3896_ = v___x_3956_;
goto v___jp_3893_;
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
v_a_3959_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3950_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3950_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
lean_ctor_set_tag(v___x_3961_, 0);
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
v___y_3894_ = v_a_3907_;
v___y_3895_ = v___x_3940_;
v_a_3896_ = v___x_3964_;
goto v___jp_3893_;
}
}
}
}
}
}
}
}
}
v___jp_3393_:
{
lean_object* v___x_3402_; uint8_t v___x_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; 
v___x_3402_ = l_Array_append___redArg(v_xs_3374_, v___y_3396_);
lean_dec_ref(v___y_3396_);
v___x_3403_ = 0;
v___x_3404_ = 1;
v___x_3405_ = l_Lean_Meta_mkForallFVars(v___x_3402_, v_type_3392_, v___x_3403_, v___y_3395_, v___y_3395_, v___x_3404_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v___x_3407_ = l_Lean_Meta_mkLambdaFVars(v___x_3402_, v___y_3397_, v___x_3403_, v___y_3395_, v___x_3403_, v___y_3395_, v___x_3404_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec_ref(v___x_3402_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3417_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_a_3408_);
lean_ctor_set(v___x_3412_, 1, v___y_3394_);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v_a_3406_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3413_);
v___x_3415_ = v___x_3410_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_a_3406_);
lean_dec(v___y_3394_);
v_a_3418_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3407_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3407_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v___x_3402_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3394_);
v_a_3426_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3405_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3405_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
v___jp_3434_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___y_3440_);
lean_ctor_set(v___x_3446_, 1, v___y_3445_);
lean_inc(v___y_3435_);
v___x_3447_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3435_, v___x_3446_, v___y_3442_, v___y_3441_, v___y_3437_, v___y_3444_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_dec_ref(v___x_3447_);
v___y_3394_ = v___y_3436_;
v___y_3395_ = v___y_3439_;
v___y_3396_ = v___y_3438_;
v___y_3397_ = v___y_3443_;
v___y_3398_ = v___y_3442_;
v___y_3399_ = v___y_3441_;
v___y_3400_ = v___y_3437_;
v___y_3401_ = v___y_3444_;
goto v___jp_3393_;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v___y_3443_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3436_);
lean_dec_ref(v_type_3392_);
lean_dec_ref(v_xs_3374_);
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
v___jp_3456_:
{
uint8_t v___x_3468_; 
v___x_3468_ = lean_nat_dec_eq(v___y_3458_, v___y_3467_);
lean_dec(v___y_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec_ref(v___y_3465_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v_type_3392_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v___x_3469_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3470_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3469_, v___y_3457_, v___y_3462_, v___y_3464_, v___y_3463_, v___y_3460_, v___y_3466_);
return v___x_3470_;
}
else
{
lean_object* v_options_3471_; uint8_t v_hasTrace_3472_; 
v_options_3471_ = lean_ctor_get(v___y_3460_, 2);
v_hasTrace_3472_ = lean_ctor_get_uint8(v_options_3471_, sizeof(void*)*1);
if (v_hasTrace_3472_ == 0)
{
lean_dec(v___y_3458_);
lean_dec(v___x_3375_);
v___y_3394_ = v___y_3459_;
v___y_3395_ = v___x_3468_;
v___y_3396_ = v___y_3461_;
v___y_3397_ = v___y_3465_;
v___y_3398_ = v___y_3464_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3460_;
v___y_3401_ = v___y_3466_;
goto v___jp_3393_;
}
else
{
lean_object* v_inheritedTraceOptions_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v_inheritedTraceOptions_3473_ = lean_ctor_get(v___y_3460_, 13);
v___x_3474_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3475_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3476_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3473_, v_options_3471_, v___x_3475_);
if (v___x_3476_ == 0)
{
lean_dec(v___y_3458_);
lean_dec(v___x_3375_);
v___y_3394_ = v___y_3459_;
v___y_3395_ = v___x_3468_;
v___y_3396_ = v___y_3461_;
v___y_3397_ = v___y_3465_;
v___y_3398_ = v___y_3464_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3460_;
v___y_3401_ = v___y_3466_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3477_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3478_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3465_);
v___x_3479_ = l_Lean_inlineExpr(v___y_3465_, v___x_3478_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3477_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_nat_dec_eq(v___y_3458_, v___x_3375_);
lean_dec(v___x_3375_);
lean_dec(v___y_3458_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3482_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3461_);
v___x_3483_ = lean_array_to_list(v___y_3461_);
v___x_3484_ = lean_box(0);
v___x_3485_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3483_, v___x_3484_);
v___x_3486_ = l_Lean_MessageData_ofList(v___x_3485_);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3482_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___y_3435_ = v___x_3474_;
v___y_3436_ = v___y_3459_;
v___y_3437_ = v___y_3460_;
v___y_3438_ = v___y_3461_;
v___y_3439_ = v___x_3468_;
v___y_3440_ = v___x_3480_;
v___y_3441_ = v___y_3463_;
v___y_3442_ = v___y_3464_;
v___y_3443_ = v___y_3465_;
v___y_3444_ = v___y_3466_;
v___y_3445_ = v___x_3489_;
goto v___jp_3434_;
}
else
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3435_ = v___x_3474_;
v___y_3436_ = v___y_3459_;
v___y_3437_ = v___y_3460_;
v___y_3438_ = v___y_3461_;
v___y_3439_ = v___x_3468_;
v___y_3440_ = v___x_3480_;
v___y_3441_ = v___y_3463_;
v___y_3442_ = v___y_3464_;
v___y_3443_ = v___y_3465_;
v___y_3444_ = v___y_3466_;
v___y_3445_ = v___x_3490_;
goto v___jp_3434_;
}
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = lean_box(1);
lean_inc_ref(v___y_3498_);
v___x_3501_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3500_, v_localInst2Index_3381_, v___y_3498_);
v___x_3502_ = lean_array_get_size(v___y_3499_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_size_3503_; 
v_size_3503_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_size_3503_);
v___y_3457_ = v___y_3492_;
v___y_3458_ = v___x_3502_;
v___y_3459_ = v___x_3501_;
v___y_3460_ = v___y_3493_;
v___y_3461_ = v___y_3499_;
v___y_3462_ = v___y_3494_;
v___y_3463_ = v___y_3496_;
v___y_3464_ = v___y_3495_;
v___y_3465_ = v___y_3498_;
v___y_3466_ = v___y_3497_;
v___y_3467_ = v_size_3503_;
goto v___jp_3456_;
}
else
{
lean_inc(v___x_3375_);
v___y_3457_ = v___y_3492_;
v___y_3458_ = v___x_3502_;
v___y_3459_ = v___x_3501_;
v___y_3460_ = v___y_3493_;
v___y_3461_ = v___y_3499_;
v___y_3462_ = v___y_3494_;
v___y_3463_ = v___y_3496_;
v___y_3464_ = v___y_3495_;
v___y_3465_ = v___y_3498_;
v___y_3466_ = v___y_3497_;
v___y_3467_ = v___x_3375_;
goto v___jp_3456_;
}
}
v___jp_3504_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3512_ = lean_array_get_size(v_insts_3380_);
v___x_3513_ = lean_mk_empty_array_with_capacity(v___x_3375_);
v___x_3514_ = lean_nat_dec_lt(v___x_3375_, v___x_3512_);
if (v___x_3514_ == 0)
{
lean_dec(v___x_3376_);
v___y_3492_ = v___y_3506_;
v___y_3493_ = v___y_3510_;
v___y_3494_ = v___y_3507_;
v___y_3495_ = v___y_3508_;
v___y_3496_ = v___y_3509_;
v___y_3497_ = v___y_3511_;
v___y_3498_ = v___y_3505_;
v___y_3499_ = v___x_3513_;
goto v___jp_3491_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v_visitedExpr_3519_; uint8_t v___x_3520_; 
v___x_3515_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
lean_inc(v___x_3375_);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3375_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
lean_inc_ref(v___x_3513_);
v___x_3517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v___x_3376_);
lean_ctor_set(v___x_3517_, 2, v___x_3513_);
lean_inc_ref(v___y_3505_);
v___x_3518_ = l_Lean_collectFVars(v___x_3517_, v___y_3505_);
v_visitedExpr_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc_ref(v_visitedExpr_3519_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = lean_nat_dec_le(v___x_3512_, v___x_3512_);
if (v___x_3520_ == 0)
{
if (v___x_3514_ == 0)
{
lean_dec_ref(v_visitedExpr_3519_);
v___y_3492_ = v___y_3506_;
v___y_3493_ = v___y_3510_;
v___y_3494_ = v___y_3507_;
v___y_3495_ = v___y_3508_;
v___y_3496_ = v___y_3509_;
v___y_3497_ = v___y_3511_;
v___y_3498_ = v___y_3505_;
v___y_3499_ = v___x_3513_;
goto v___jp_3491_;
}
else
{
size_t v___x_3521_; size_t v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = lean_usize_of_nat(v___x_3512_);
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3519_, v_insts_3380_, v___x_3521_, v___x_3522_, v___x_3513_);
lean_dec_ref(v_visitedExpr_3519_);
v___y_3492_ = v___y_3506_;
v___y_3493_ = v___y_3510_;
v___y_3494_ = v___y_3507_;
v___y_3495_ = v___y_3508_;
v___y_3496_ = v___y_3509_;
v___y_3497_ = v___y_3511_;
v___y_3498_ = v___y_3505_;
v___y_3499_ = v___x_3523_;
goto v___jp_3491_;
}
}
else
{
size_t v___x_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = ((size_t)0ULL);
v___x_3525_ = lean_usize_of_nat(v___x_3512_);
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3519_, v_insts_3380_, v___x_3524_, v___x_3525_, v___x_3513_);
lean_dec_ref(v_visitedExpr_3519_);
v___y_3492_ = v___y_3506_;
v___y_3493_ = v___y_3510_;
v___y_3494_ = v___y_3507_;
v___y_3495_ = v___y_3508_;
v___y_3496_ = v___y_3509_;
v___y_3497_ = v___y_3511_;
v___y_3498_ = v___y_3505_;
v___y_3499_ = v___x_3526_;
goto v___jp_3491_;
}
}
}
v___jp_3527_:
{
lean_object* v___x_3535_; 
lean_inc_ref(v_val_3528_);
v___x_3535_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3536_; lean_object* v_a_3537_; uint8_t v___x_3538_; 
lean_dec_ref(v___x_3535_);
v___x_3536_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3528_, v___y_3532_);
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = l_Lean_Expr_hasMVar(v_a_3537_);
if (v___x_3538_ == 0)
{
v___y_3505_ = v_a_3537_;
v___y_3506_ = v___y_3529_;
v___y_3507_ = v___y_3530_;
v___y_3508_ = v___y_3531_;
v___y_3509_ = v___y_3532_;
v___y_3510_ = v___y_3533_;
v___y_3511_ = v___y_3534_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v___x_3539_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13);
v___x_3540_ = lean_unsigned_to_nat(30u);
v___x_3541_ = l_Lean_inlineExprTrailing(v_a_3537_, v___x_3540_);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3539_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3542_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec_ref(v_val_3528_);
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v_a_3552_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3535_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3535_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
v___jp_3560_:
{
if (lean_obj_tag(v___y_3561_) == 0)
{
lean_object* v_a_3562_; 
v_a_3562_ = lean_ctor_get(v___y_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref(v___y_3561_);
v_val_3528_ = v_a_3562_;
v___y_3529_ = v___y_3382_;
v___y_3530_ = v___y_3383_;
v___y_3531_ = v___y_3384_;
v___y_3532_ = v___y_3385_;
v___y_3533_ = v___y_3386_;
v___y_3534_ = v___y_3387_;
goto v___jp_3527_;
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v_a_3563_ = lean_ctor_get(v___y_3561_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___y_3561_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___y_3561_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___y_3561_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
v___jp_3571_:
{
if (lean_obj_tag(v___y_3572_) == 0)
{
lean_object* v_a_3573_; 
v_a_3573_ = lean_ctor_get(v___y_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___y_3572_);
v_val_3528_ = v_a_3573_;
v___y_3529_ = v___y_3382_;
v___y_3530_ = v___y_3383_;
v___y_3531_ = v___y_3384_;
v___y_3532_ = v___y_3385_;
v___y_3533_ = v___y_3386_;
v___y_3534_ = v___y_3387_;
goto v___jp_3527_;
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec_ref(v_type_3392_);
lean_dec(v_localInst2Index_3381_);
lean_dec(v___x_3376_);
lean_dec(v___x_3375_);
lean_dec_ref(v_xs_3374_);
v_a_3574_ = lean_ctor_get(v___y_3572_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___y_3572_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___y_3572_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___y_3572_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_3979_ = _args[0];
lean_object* v_us_3980_ = _args[1];
lean_object* v_xs_3981_ = _args[2];
lean_object* v___x_3982_ = _args[3];
lean_object* v___x_3983_ = _args[4];
lean_object* v_ctorName_3984_ = _args[5];
lean_object* v___x_3985_ = _args[6];
lean_object* v___f_3986_ = _args[7];
lean_object* v_insts_3987_ = _args[8];
lean_object* v_localInst2Index_3988_ = _args[9];
lean_object* v___y_3989_ = _args[10];
lean_object* v___y_3990_ = _args[11];
lean_object* v___y_3991_ = _args[12];
lean_object* v___y_3992_ = _args[13];
lean_object* v___y_3993_ = _args[14];
lean_object* v___y_3994_ = _args[15];
lean_object* v___y_3995_ = _args[16];
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_3979_, v_us_3980_, v_xs_3981_, v___x_3982_, v___x_3983_, v_ctorName_3984_, v___x_3985_, v___f_3986_, v_insts_3987_, v_localInst2Index_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec_ref(v_insts_3987_);
lean_dec_ref(v___x_3985_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_3997_, size_t v_i_3998_, lean_object* v_bs_3999_){
_start:
{
uint8_t v___x_4000_; 
v___x_4000_ = lean_usize_dec_lt(v_i_3998_, v_sz_3997_);
if (v___x_4000_ == 0)
{
return v_bs_3999_;
}
else
{
lean_object* v_v_4001_; lean_object* v___x_4002_; lean_object* v_bs_x27_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; size_t v___x_4008_; size_t v___x_4009_; lean_object* v___x_4010_; 
v_v_4001_ = lean_array_uget(v_bs_3999_, v_i_3998_);
v___x_4002_ = lean_unsigned_to_nat(0u);
v_bs_x27_4003_ = lean_array_uset(v_bs_3999_, v_i_3998_, v___x_4002_);
v___x_4004_ = l_Lean_Expr_fvarId_x21(v_v_4001_);
lean_dec(v_v_4001_);
v___x_4005_ = 1;
v___x_4006_ = lean_box(v___x_4005_);
v___x_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4004_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
v___x_4008_ = ((size_t)1ULL);
v___x_4009_ = lean_usize_add(v_i_3998_, v___x_4008_);
v___x_4010_ = lean_array_uset(v_bs_x27_4003_, v_i_3998_, v___x_4007_);
v_i_3998_ = v___x_4009_;
v_bs_3999_ = v___x_4010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_4012_, lean_object* v_i_4013_, lean_object* v_bs_4014_){
_start:
{
size_t v_sz_boxed_4015_; size_t v_i_boxed_4016_; lean_object* v_res_4017_; 
v_sz_boxed_4015_ = lean_unbox_usize(v_sz_4012_);
lean_dec(v_sz_4012_);
v_i_boxed_4016_ = lean_unbox_usize(v_i_4013_);
lean_dec(v_i_4013_);
v_res_4017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_4015_, v_i_boxed_4016_, v_bs_4014_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; 
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
v___x_4026_ = lean_apply_7(v_k_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, lean_box(0));
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_4036_, lean_object* v_k_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v___f_4045_; lean_object* v___x_4046_; 
lean_inc(v___y_4039_);
lean_inc_ref(v___y_4038_);
v___f_4045_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4045_, 0, v_k_4037_);
lean_closure_set(v___f_4045_, 1, v___y_4038_);
lean_closure_set(v___f_4045_, 2, v___y_4039_);
v___x_4046_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_4036_, v___f_4045_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
if (lean_obj_tag(v___x_4046_) == 0)
{
return v___x_4046_;
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4055_, lean_object* v_k_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4055_, v_k_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec_ref(v_bs_4055_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4065_, lean_object* v_k_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
size_t v_sz_4074_; size_t v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_sz_4074_ = lean_array_size(v_bs_4065_);
v___x_4075_ = ((size_t)0ULL);
v___x_4076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4074_, v___x_4075_, v_bs_4065_);
v___x_4077_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4076_, v_k_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec_ref(v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4078_, lean_object* v_k_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4078_, v_k_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4088_, lean_object* v_inductiveTypeName_4089_, lean_object* v_us_4090_, lean_object* v___x_4091_, lean_object* v_ctorName_4092_, lean_object* v___f_4093_, uint8_t v_addHypotheses_4094_, lean_object* v_xs_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___f_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4104_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4095_, 2);
v___x_4105_ = l_Array_toSubarray___redArg(v_xs_4095_, v___x_4104_, v_numParams_4088_);
v___x_4106_ = l_Subarray_copy___redArg(v___x_4105_);
lean_inc_ref(v___x_4106_);
v___f_4107_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4107_, 0, v_inductiveTypeName_4089_);
lean_closure_set(v___f_4107_, 1, v_us_4090_);
lean_closure_set(v___f_4107_, 2, v_xs_4095_);
lean_closure_set(v___f_4107_, 3, v___x_4104_);
lean_closure_set(v___f_4107_, 4, v___x_4091_);
lean_closure_set(v___f_4107_, 5, v_ctorName_4092_);
lean_closure_set(v___f_4107_, 6, v___x_4106_);
lean_closure_set(v___f_4107_, 7, v___f_4093_);
v___x_4108_ = lean_box(v_addHypotheses_4094_);
v___x_4109_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4109_, 0, v___x_4108_);
lean_closure_set(v___x_4109_, 1, lean_box(0));
lean_closure_set(v___x_4109_, 2, v___x_4106_);
lean_closure_set(v___x_4109_, 3, v___f_4107_);
v___x_4110_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4095_, v___x_4109_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4111_, lean_object* v_inductiveTypeName_4112_, lean_object* v_us_4113_, lean_object* v___x_4114_, lean_object* v_ctorName_4115_, lean_object* v___f_4116_, lean_object* v_addHypotheses_4117_, lean_object* v_xs_4118_, lean_object* v_x_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
uint8_t v_addHypotheses_boxed_4127_; lean_object* v_res_4128_; 
v_addHypotheses_boxed_4127_ = lean_unbox(v_addHypotheses_4117_);
v_res_4128_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4111_, v_inductiveTypeName_4112_, v_us_4113_, v___x_4114_, v_ctorName_4115_, v___f_4116_, v_addHypotheses_boxed_4127_, v_xs_4118_, v_x_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec_ref(v_x_4119_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
if (lean_obj_tag(v_a_4129_) == 0)
{
lean_object* v___x_4131_; 
v___x_4131_ = l_List_reverse___redArg(v_a_4130_);
return v___x_4131_;
}
else
{
lean_object* v_head_4132_; lean_object* v_tail_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4142_; 
v_head_4132_ = lean_ctor_get(v_a_4129_, 0);
v_tail_4133_ = lean_ctor_get(v_a_4129_, 1);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_a_4129_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4135_ = v_a_4129_;
v_isShared_4136_ = v_isSharedCheck_4142_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_tail_4133_);
lean_inc(v_head_4132_);
lean_dec(v_a_4129_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4142_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4137_ = l_Lean_Level_param___override(v_head_4132_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 1, v_a_4130_);
lean_ctor_set(v___x_4135_, 0, v___x_4137_);
v___x_4139_ = v___x_4135_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v_a_4130_);
v___x_4139_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
v_a_4129_ = v_tail_4133_;
v_a_4130_ = v___x_4139_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4144_, lean_object* v_ctorName_4145_, uint8_t v_addHypotheses_4146_, lean_object* v_indVal_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_toConstantVal_4155_; lean_object* v_numParams_4156_; lean_object* v_levelParams_4157_; lean_object* v_type_4158_; lean_object* v___f_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v_us_4162_; lean_object* v___x_4163_; lean_object* v___f_4164_; uint8_t v___x_4165_; lean_object* v___x_4166_; 
v_toConstantVal_4155_ = lean_ctor_get(v_indVal_4147_, 0);
lean_inc_ref(v_toConstantVal_4155_);
v_numParams_4156_ = lean_ctor_get(v_indVal_4147_, 1);
lean_inc(v_numParams_4156_);
lean_dec_ref(v_indVal_4147_);
v_levelParams_4157_ = lean_ctor_get(v_toConstantVal_4155_, 1);
lean_inc(v_levelParams_4157_);
v_type_4158_ = lean_ctor_get(v_toConstantVal_4155_, 2);
lean_inc_ref(v_type_4158_);
lean_dec_ref(v_toConstantVal_4155_);
v___f_4159_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4160_ = lean_box(1);
v___x_4161_ = lean_box(0);
v_us_4162_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4157_, v___x_4161_);
v___x_4163_ = lean_box(v_addHypotheses_4146_);
v___f_4164_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4164_, 0, v_numParams_4156_);
lean_closure_set(v___f_4164_, 1, v_inductiveTypeName_4144_);
lean_closure_set(v___f_4164_, 2, v_us_4162_);
lean_closure_set(v___f_4164_, 3, v___x_4160_);
lean_closure_set(v___f_4164_, 4, v_ctorName_4145_);
lean_closure_set(v___f_4164_, 5, v___f_4159_);
lean_closure_set(v___f_4164_, 6, v___x_4163_);
v___x_4165_ = 0;
v___x_4166_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4158_, v___f_4164_, v___x_4165_, v___x_4165_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4167_, lean_object* v_ctorName_4168_, lean_object* v_addHypotheses_4169_, lean_object* v_indVal_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
uint8_t v_addHypotheses_boxed_4178_; lean_object* v_res_4179_; 
v_addHypotheses_boxed_4178_ = lean_unbox(v_addHypotheses_4169_);
v_res_4179_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4167_, v_ctorName_4168_, v_addHypotheses_boxed_4178_, v_indVal_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4180_, lean_object* v_bs_4181_, lean_object* v_k_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4181_, v_k_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4191_, lean_object* v_bs_4192_, lean_object* v_k_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4191_, v_bs_4192_, v_k_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec_ref(v_bs_4192_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4202_, lean_object* v_bs_4203_, lean_object* v_k_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4203_, v_k_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4213_, lean_object* v_bs_4214_, lean_object* v_k_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4213_, v_bs_4214_, v_k_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4224_, lean_object* v_levelParams_4225_, lean_object* v_type_4226_, lean_object* v_value_4227_, lean_object* v_hints_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; uint8_t v___y_4233_; uint8_t v___y_4240_; lean_object* v_env_4243_; uint8_t v___x_4244_; 
v___x_4231_ = lean_st_ref_get(v___y_4229_);
v_env_4243_ = lean_ctor_get(v___x_4231_, 0);
lean_inc_ref_n(v_env_4243_, 2);
lean_dec(v___x_4231_);
v___x_4244_ = l_Lean_Environment_hasUnsafe(v_env_4243_, v_type_4226_);
if (v___x_4244_ == 0)
{
uint8_t v___x_4245_; 
v___x_4245_ = l_Lean_Environment_hasUnsafe(v_env_4243_, v_value_4227_);
v___y_4240_ = v___x_4245_;
goto v___jp_4239_;
}
else
{
lean_dec_ref(v_env_4243_);
v___y_4240_ = v___x_4244_;
goto v___jp_4239_;
}
v___jp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_inc(v_name_4224_);
v___x_4234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4234_, 0, v_name_4224_);
lean_ctor_set(v___x_4234_, 1, v_levelParams_4225_);
lean_ctor_set(v___x_4234_, 2, v_type_4226_);
v___x_4235_ = lean_box(0);
v___x_4236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4236_, 0, v_name_4224_);
lean_ctor_set(v___x_4236_, 1, v___x_4235_);
v___x_4237_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4237_, 0, v___x_4234_);
lean_ctor_set(v___x_4237_, 1, v_value_4227_);
lean_ctor_set(v___x_4237_, 2, v_hints_4228_);
lean_ctor_set(v___x_4237_, 3, v___x_4236_);
lean_ctor_set_uint8(v___x_4237_, sizeof(void*)*4, v___y_4233_);
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
v___jp_4239_:
{
if (v___y_4240_ == 0)
{
uint8_t v___x_4241_; 
v___x_4241_ = 1;
v___y_4233_ = v___x_4241_;
goto v___jp_4232_;
}
else
{
uint8_t v___x_4242_; 
v___x_4242_ = 0;
v___y_4233_ = v___x_4242_;
goto v___jp_4232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4246_, lean_object* v_levelParams_4247_, lean_object* v_type_4248_, lean_object* v_value_4249_, lean_object* v_hints_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4246_, v_levelParams_4247_, v_type_4248_, v_value_4249_, v_hints_4250_, v___y_4251_);
lean_dec(v___y_4251_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4254_, lean_object* v_levelParams_4255_, lean_object* v_type_4256_, lean_object* v_value_4257_, lean_object* v_hints_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4254_, v_levelParams_4255_, v_type_4256_, v_value_4257_, v_hints_4258_, v___y_4264_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4267_, lean_object* v_levelParams_4268_, lean_object* v_type_4269_, lean_object* v_value_4270_, lean_object* v_hints_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4267_, v_levelParams_4268_, v_type_4269_, v_value_4270_, v_hints_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4280_, uint8_t v_isExporting_4281_, lean_object* v___x_4282_, lean_object* v___y_4283_, lean_object* v___x_4284_, lean_object* v_a_x3f_4285_){
_start:
{
lean_object* v___x_4287_; lean_object* v_env_4288_; lean_object* v_nextMacroScope_4289_; lean_object* v_ngen_4290_; lean_object* v_auxDeclNGen_4291_; lean_object* v_traceState_4292_; lean_object* v_messages_4293_; lean_object* v_infoState_4294_; lean_object* v_snapshotTasks_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4320_; 
v___x_4287_ = lean_st_ref_take(v___y_4280_);
v_env_4288_ = lean_ctor_get(v___x_4287_, 0);
v_nextMacroScope_4289_ = lean_ctor_get(v___x_4287_, 1);
v_ngen_4290_ = lean_ctor_get(v___x_4287_, 2);
v_auxDeclNGen_4291_ = lean_ctor_get(v___x_4287_, 3);
v_traceState_4292_ = lean_ctor_get(v___x_4287_, 4);
v_messages_4293_ = lean_ctor_get(v___x_4287_, 6);
v_infoState_4294_ = lean_ctor_get(v___x_4287_, 7);
v_snapshotTasks_4295_ = lean_ctor_get(v___x_4287_, 8);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4320_ == 0)
{
lean_object* v_unused_4321_; 
v_unused_4321_ = lean_ctor_get(v___x_4287_, 5);
lean_dec(v_unused_4321_);
v___x_4297_ = v___x_4287_;
v_isShared_4298_ = v_isSharedCheck_4320_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_snapshotTasks_4295_);
lean_inc(v_infoState_4294_);
lean_inc(v_messages_4293_);
lean_inc(v_traceState_4292_);
lean_inc(v_auxDeclNGen_4291_);
lean_inc(v_ngen_4290_);
lean_inc(v_nextMacroScope_4289_);
lean_inc(v_env_4288_);
lean_dec(v___x_4287_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4320_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4299_ = l_Lean_Environment_setExporting(v_env_4288_, v_isExporting_4281_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 5, v___x_4282_);
lean_ctor_set(v___x_4297_, 0, v___x_4299_);
v___x_4301_ = v___x_4297_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4299_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_nextMacroScope_4289_);
lean_ctor_set(v_reuseFailAlloc_4319_, 2, v_ngen_4290_);
lean_ctor_set(v_reuseFailAlloc_4319_, 3, v_auxDeclNGen_4291_);
lean_ctor_set(v_reuseFailAlloc_4319_, 4, v_traceState_4292_);
lean_ctor_set(v_reuseFailAlloc_4319_, 5, v___x_4282_);
lean_ctor_set(v_reuseFailAlloc_4319_, 6, v_messages_4293_);
lean_ctor_set(v_reuseFailAlloc_4319_, 7, v_infoState_4294_);
lean_ctor_set(v_reuseFailAlloc_4319_, 8, v_snapshotTasks_4295_);
v___x_4301_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v_mctx_4304_; lean_object* v_zetaDeltaFVarIds_4305_; lean_object* v_postponed_4306_; lean_object* v_diag_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4317_; 
v___x_4302_ = lean_st_ref_set(v___y_4280_, v___x_4301_);
v___x_4303_ = lean_st_ref_take(v___y_4283_);
v_mctx_4304_ = lean_ctor_get(v___x_4303_, 0);
v_zetaDeltaFVarIds_4305_ = lean_ctor_get(v___x_4303_, 2);
v_postponed_4306_ = lean_ctor_get(v___x_4303_, 3);
v_diag_4307_ = lean_ctor_get(v___x_4303_, 4);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; 
v_unused_4318_ = lean_ctor_get(v___x_4303_, 1);
lean_dec(v_unused_4318_);
v___x_4309_ = v___x_4303_;
v_isShared_4310_ = v_isSharedCheck_4317_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_diag_4307_);
lean_inc(v_postponed_4306_);
lean_inc(v_zetaDeltaFVarIds_4305_);
lean_inc(v_mctx_4304_);
lean_dec(v___x_4303_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4317_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 1, v___x_4284_);
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_mctx_4304_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4316_, 2, v_zetaDeltaFVarIds_4305_);
lean_ctor_set(v_reuseFailAlloc_4316_, 3, v_postponed_4306_);
lean_ctor_set(v_reuseFailAlloc_4316_, 4, v_diag_4307_);
v___x_4312_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4313_ = lean_st_ref_set(v___y_4283_, v___x_4312_);
v___x_4314_ = lean_box(0);
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4322_, lean_object* v_isExporting_4323_, lean_object* v___x_4324_, lean_object* v___y_4325_, lean_object* v___x_4326_, lean_object* v_a_x3f_4327_, lean_object* v___y_4328_){
_start:
{
uint8_t v_isExporting_boxed_4329_; lean_object* v_res_4330_; 
v_isExporting_boxed_4329_ = lean_unbox(v_isExporting_4323_);
v_res_4330_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4322_, v_isExporting_boxed_4329_, v___x_4324_, v___y_4325_, v___x_4326_, v_a_x3f_4327_);
lean_dec(v_a_x3f_4327_);
lean_dec(v___y_4325_);
lean_dec(v___y_4322_);
return v_res_4330_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4331_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
return v___x_4333_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
return v___x_4335_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
lean_ctor_set(v___x_4337_, 2, v___x_4336_);
lean_ctor_set(v___x_4337_, 3, v___x_4336_);
lean_ctor_set(v___x_4337_, 4, v___x_4336_);
lean_ctor_set(v___x_4337_, 5, v___x_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4338_, uint8_t v_isExporting_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v___x_4347_; lean_object* v_env_4348_; uint8_t v_isExporting_4349_; lean_object* v___x_4350_; lean_object* v_env_4351_; lean_object* v_nextMacroScope_4352_; lean_object* v_ngen_4353_; lean_object* v_auxDeclNGen_4354_; lean_object* v_traceState_4355_; lean_object* v_messages_4356_; lean_object* v_infoState_4357_; lean_object* v_snapshotTasks_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4412_; 
v___x_4347_ = lean_st_ref_get(v___y_4345_);
v_env_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc_ref(v_env_4348_);
lean_dec(v___x_4347_);
v_isExporting_4349_ = lean_ctor_get_uint8(v_env_4348_, sizeof(void*)*8);
lean_dec_ref(v_env_4348_);
v___x_4350_ = lean_st_ref_take(v___y_4345_);
v_env_4351_ = lean_ctor_get(v___x_4350_, 0);
v_nextMacroScope_4352_ = lean_ctor_get(v___x_4350_, 1);
v_ngen_4353_ = lean_ctor_get(v___x_4350_, 2);
v_auxDeclNGen_4354_ = lean_ctor_get(v___x_4350_, 3);
v_traceState_4355_ = lean_ctor_get(v___x_4350_, 4);
v_messages_4356_ = lean_ctor_get(v___x_4350_, 6);
v_infoState_4357_ = lean_ctor_get(v___x_4350_, 7);
v_snapshotTasks_4358_ = lean_ctor_get(v___x_4350_, 8);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; 
v_unused_4413_ = lean_ctor_get(v___x_4350_, 5);
lean_dec(v_unused_4413_);
v___x_4360_ = v___x_4350_;
v_isShared_4361_ = v_isSharedCheck_4412_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_snapshotTasks_4358_);
lean_inc(v_infoState_4357_);
lean_inc(v_messages_4356_);
lean_inc(v_traceState_4355_);
lean_inc(v_auxDeclNGen_4354_);
lean_inc(v_ngen_4353_);
lean_inc(v_nextMacroScope_4352_);
lean_inc(v_env_4351_);
lean_dec(v___x_4350_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4412_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4365_; 
v___x_4362_ = l_Lean_Environment_setExporting(v_env_4351_, v_isExporting_4339_);
v___x_4363_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 5, v___x_4363_);
lean_ctor_set(v___x_4360_, 0, v___x_4362_);
v___x_4365_ = v___x_4360_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4362_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_nextMacroScope_4352_);
lean_ctor_set(v_reuseFailAlloc_4411_, 2, v_ngen_4353_);
lean_ctor_set(v_reuseFailAlloc_4411_, 3, v_auxDeclNGen_4354_);
lean_ctor_set(v_reuseFailAlloc_4411_, 4, v_traceState_4355_);
lean_ctor_set(v_reuseFailAlloc_4411_, 5, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4411_, 6, v_messages_4356_);
lean_ctor_set(v_reuseFailAlloc_4411_, 7, v_infoState_4357_);
lean_ctor_set(v_reuseFailAlloc_4411_, 8, v_snapshotTasks_4358_);
v___x_4365_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v_mctx_4368_; lean_object* v_zetaDeltaFVarIds_4369_; lean_object* v_postponed_4370_; lean_object* v_diag_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4409_; 
v___x_4366_ = lean_st_ref_set(v___y_4345_, v___x_4365_);
v___x_4367_ = lean_st_ref_take(v___y_4343_);
v_mctx_4368_ = lean_ctor_get(v___x_4367_, 0);
v_zetaDeltaFVarIds_4369_ = lean_ctor_get(v___x_4367_, 2);
v_postponed_4370_ = lean_ctor_get(v___x_4367_, 3);
v_diag_4371_ = lean_ctor_get(v___x_4367_, 4);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4409_ == 0)
{
lean_object* v_unused_4410_; 
v_unused_4410_ = lean_ctor_get(v___x_4367_, 1);
lean_dec(v_unused_4410_);
v___x_4373_ = v___x_4367_;
v_isShared_4374_ = v_isSharedCheck_4409_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_diag_4371_);
lean_inc(v_postponed_4370_);
lean_inc(v_zetaDeltaFVarIds_4369_);
lean_inc(v_mctx_4368_);
lean_dec(v___x_4367_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4409_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4375_; lean_object* v___x_4377_; 
v___x_4375_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 1, v___x_4375_);
v___x_4377_ = v___x_4373_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_mctx_4368_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v___x_4375_);
lean_ctor_set(v_reuseFailAlloc_4408_, 2, v_zetaDeltaFVarIds_4369_);
lean_ctor_set(v_reuseFailAlloc_4408_, 3, v_postponed_4370_);
lean_ctor_set(v_reuseFailAlloc_4408_, 4, v_diag_4371_);
v___x_4377_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
lean_object* v___x_4378_; lean_object* v_r_4379_; 
v___x_4378_ = lean_st_ref_set(v___y_4343_, v___x_4377_);
lean_inc(v___y_4345_);
lean_inc_ref(v___y_4344_);
lean_inc(v___y_4343_);
lean_inc_ref(v___y_4342_);
lean_inc(v___y_4341_);
lean_inc_ref(v___y_4340_);
v_r_4379_ = lean_apply_7(v_x_4338_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, lean_box(0));
if (lean_obj_tag(v_r_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4396_; 
v_a_4380_ = lean_ctor_get(v_r_4379_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_r_4379_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4382_ = v_r_4379_;
v_isShared_4383_ = v_isSharedCheck_4396_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v_r_4379_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4396_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
lean_inc(v_a_4380_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set_tag(v___x_4382_, 1);
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v___x_4386_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4345_, v_isExporting_4349_, v___x_4363_, v___y_4343_, v___x_4375_, v___x_4385_);
lean_dec_ref(v___x_4385_);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4393_ == 0)
{
lean_object* v_unused_4394_; 
v_unused_4394_ = lean_ctor_get(v___x_4386_, 0);
lean_dec(v_unused_4394_);
v___x_4388_ = v___x_4386_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_dec(v___x_4386_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v_a_4380_);
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4380_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
v_a_4397_ = lean_ctor_get(v_r_4379_, 0);
lean_inc(v_a_4397_);
lean_dec_ref(v_r_4379_);
v___x_4398_ = lean_box(0);
v___x_4399_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4345_, v_isExporting_4349_, v___x_4363_, v___y_4343_, v___x_4375_, v___x_4398_);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4406_ == 0)
{
lean_object* v_unused_4407_; 
v_unused_4407_ = lean_ctor_get(v___x_4399_, 0);
lean_dec(v_unused_4407_);
v___x_4401_ = v___x_4399_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_dec(v___x_4399_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
lean_ctor_set_tag(v___x_4401_, 1);
lean_ctor_set(v___x_4401_, 0, v_a_4397_);
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4397_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4414_, lean_object* v_isExporting_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
uint8_t v_isExporting_boxed_4423_; lean_object* v_res_4424_; 
v_isExporting_boxed_4423_ = lean_unbox(v_isExporting_4415_);
v_res_4424_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4414_, v_isExporting_boxed_4423_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4425_, lean_object* v_x_4426_, uint8_t v_isExporting_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4426_, v_isExporting_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4436_, lean_object* v_x_4437_, lean_object* v_isExporting_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
uint8_t v_isExporting_boxed_4446_; lean_object* v_res_4447_; 
v_isExporting_boxed_4446_ = lean_unbox(v_isExporting_4438_);
v_res_4447_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4436_, v_x_4437_, v_isExporting_boxed_4446_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
return v_res_4468_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4471_ = l_Lean_stringToMessageData(v___x_4470_);
return v___x_4471_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4474_ = l_Lean_stringToMessageData(v___x_4473_);
return v___x_4474_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4477_ = l_Lean_stringToMessageData(v___x_4476_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4478_, lean_object* v___x_4479_, lean_object* v_inductiveTypeName_4480_, uint8_t v___x_4481_, lean_object* v___x_4482_, lean_object* v_ctorName_4483_, uint8_t v_addHypotheses_4484_, lean_object* v___f_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___y_4494_; lean_object* v___x_4497_; 
lean_inc(v_inductiveTypeName_4480_);
v___x_4497_ = l_Lean_Elab_Deriving_mkContext(v___x_4478_, v___x_4479_, v_inductiveTypeName_4480_, v___x_4481_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v_options_4499_; lean_object* v_currNamespace_4500_; lean_object* v_inheritedTraceOptions_4501_; lean_object* v___x_4502_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref(v___x_4497_);
v_options_4499_ = lean_ctor_get(v___y_4490_, 2);
v_currNamespace_4500_ = lean_ctor_get(v___y_4490_, 6);
v_inheritedTraceOptions_4501_ = lean_ctor_get(v___y_4490_, 13);
lean_inc(v_inductiveTypeName_4480_);
v___x_4502_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4480_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v_instName_4504_; lean_object* v_auxFunNames_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4550_; uint8_t v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4586_; uint8_t v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v_a_4608_; lean_object* v___y_4679_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc_n(v_a_4503_, 2);
lean_dec_ref(v___x_4502_);
v_instName_4504_ = lean_ctor_get(v_a_4498_, 0);
lean_inc(v_instName_4504_);
v_auxFunNames_4505_ = lean_ctor_get(v_a_4498_, 2);
lean_inc_ref(v_auxFunNames_4505_);
lean_dec(v_a_4498_);
v___x_4506_ = lean_unsigned_to_nat(0u);
v___x_4507_ = lean_array_get(v___x_4482_, v_auxFunNames_4505_, v___x_4506_);
lean_dec_ref(v_auxFunNames_4505_);
lean_inc(v_currNamespace_4500_);
v___x_4508_ = l_Lean_Name_append(v_currNamespace_4500_, v___x_4507_);
v___x_4698_ = lean_box(v_addHypotheses_4484_);
lean_inc(v_inductiveTypeName_4480_);
v___x_4699_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4699_, 0, v_inductiveTypeName_4480_);
lean_closure_set(v___x_4699_, 1, v_ctorName_4483_);
lean_closure_set(v___x_4699_, 2, v___x_4698_);
lean_closure_set(v___x_4699_, 3, v_a_4503_);
lean_inc(v___x_4508_);
v___x_4700_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4508_, v___x_4699_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; 
lean_dec_ref(v___f_4485_);
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref(v___x_4700_);
v_a_4608_ = v_a_4701_;
goto v___jp_4607_;
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4734_; 
v_a_4702_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4704_ = v___x_4700_;
v_isShared_4705_ = v_isSharedCheck_4734_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4700_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4734_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
uint8_t v___y_4710_; uint8_t v___x_4732_; 
v___x_4732_ = l_Lean_Exception_isInterrupt(v_a_4702_);
if (v___x_4732_ == 0)
{
uint8_t v___x_4733_; 
lean_inc(v_a_4702_);
v___x_4733_ = l_Lean_Exception_isRuntime(v_a_4702_);
v___y_4710_ = v___x_4733_;
goto v___jp_4709_;
}
else
{
v___y_4710_ = v___x_4732_;
goto v___jp_4709_;
}
v___jp_4706_:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = lean_box(0);
lean_inc(v___y_4491_);
lean_inc_ref(v___y_4490_);
lean_inc(v___y_4489_);
lean_inc_ref(v___y_4488_);
lean_inc(v___y_4487_);
lean_inc_ref(v___y_4486_);
v___x_4708_ = lean_apply_8(v___f_4485_, v___x_4707_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, lean_box(0));
v___y_4679_ = v___x_4708_;
goto v___jp_4678_;
}
v___jp_4709_:
{
if (v___y_4710_ == 0)
{
uint8_t v_hasTrace_4711_; 
lean_del_object(v___x_4704_);
v_hasTrace_4711_ = lean_ctor_get_uint8(v_options_4499_, sizeof(void*)*1);
if (v_hasTrace_4711_ == 0)
{
lean_dec(v_a_4702_);
goto v___jp_4706_;
}
else
{
lean_object* v___x_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___x_4712_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4713_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4714_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4501_, v_options_4499_, v___x_4713_);
if (v___x_4714_ == 0)
{
lean_dec(v_a_4702_);
goto v___jp_4706_;
}
else
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4715_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4716_ = l_Lean_Exception_toMessageData(v_a_4702_);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4712_, v___x_4717_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4720_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref(v___x_4718_);
lean_inc(v___y_4491_);
lean_inc_ref(v___y_4490_);
lean_inc(v___y_4489_);
lean_inc_ref(v___y_4488_);
lean_inc(v___y_4487_);
lean_inc_ref(v___y_4486_);
v___x_4720_ = lean_apply_8(v___f_4485_, v_a_4719_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, lean_box(0));
v___y_4679_ = v___x_4720_;
goto v___jp_4678_;
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v_a_4503_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v___f_4485_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4721_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4718_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4718_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
}
else
{
lean_object* v___x_4730_; 
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v_a_4503_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v___f_4485_);
lean_dec(v_inductiveTypeName_4480_);
if (v_isShared_4705_ == 0)
{
v___x_4730_ = v___x_4704_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4702_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
}
v___jp_4509_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4518_ = lean_mk_syntax_ident(v_instName_4504_);
v___x_4519_ = l_Lean_mkCIdent(v___x_4508_);
v___x_4520_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4480_, v___x_4518_, v___y_4511_, v___x_4519_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_options_4521_; uint8_t v_hasTrace_4522_; 
v_options_4521_ = lean_ctor_get(v___y_4516_, 2);
v_hasTrace_4522_ = lean_ctor_get_uint8(v_options_4521_, sizeof(void*)*1);
if (v_hasTrace_4522_ == 0)
{
lean_object* v_a_4523_; 
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4510_);
v_a_4523_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4523_);
lean_dec_ref(v___x_4520_);
v___y_4494_ = v_a_4523_;
goto v___jp_4493_;
}
else
{
lean_object* v_a_4524_; lean_object* v_inheritedTraceOptions_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v_a_4524_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4524_);
lean_dec_ref(v___x_4520_);
v_inheritedTraceOptions_4525_ = lean_ctor_get(v___y_4516_, 13);
v___x_4526_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4510_);
v___x_4527_ = l_Lean_Name_append(v___x_4526_, v___y_4510_);
v___x_4528_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4525_, v_options_4521_, v___x_4527_);
lean_dec(v___x_4527_);
if (v___x_4528_ == 0)
{
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4510_);
v___y_4494_ = v_a_4524_;
goto v___jp_4493_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4529_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4524_);
v___x_4530_ = l_Lean_MessageData_ofSyntax(v_a_4524_);
v___x_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4529_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
v___x_4532_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4510_, v___x_4531_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_dec_ref(v___x_4532_);
v___y_4494_ = v_a_4524_;
goto v___jp_4493_;
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec(v_a_4524_);
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4510_);
v_a_4541_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4520_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4520_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
v___jp_4549_:
{
lean_object* v___x_4558_; 
lean_inc(v___x_4508_);
v___x_4558_ = l_Lean_enableRealizationsForConst(v___x_4508_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_options_4559_; lean_object* v_inheritedTraceOptions_4560_; uint8_t v_hasTrace_4561_; lean_object* v___x_4562_; 
lean_dec_ref(v___x_4558_);
v_options_4559_ = lean_ctor_get(v___y_4556_, 2);
v_inheritedTraceOptions_4560_ = lean_ctor_get(v___y_4556_, 13);
v_hasTrace_4561_ = lean_ctor_get_uint8(v_options_4559_, sizeof(void*)*1);
v___x_4562_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4561_ == 0)
{
v___y_4510_ = v___x_4562_;
v___y_4511_ = v___y_4550_;
v___y_4512_ = v___y_4552_;
v___y_4513_ = v___y_4553_;
v___y_4514_ = v___y_4554_;
v___y_4515_ = v___y_4555_;
v___y_4516_ = v___y_4556_;
v___y_4517_ = v___y_4557_;
goto v___jp_4509_;
}
else
{
lean_object* v___x_4563_; uint8_t v___x_4564_; 
v___x_4563_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4560_, v_options_4559_, v___x_4563_);
if (v___x_4564_ == 0)
{
v___y_4510_ = v___x_4562_;
v___y_4511_ = v___y_4550_;
v___y_4512_ = v___y_4552_;
v___y_4513_ = v___y_4553_;
v___y_4514_ = v___y_4554_;
v___y_4515_ = v___y_4555_;
v___y_4516_ = v___y_4556_;
v___y_4517_ = v___y_4557_;
goto v___jp_4509_;
}
else
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4565_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4508_);
v___x_4566_ = l_Lean_MessageData_ofConstName(v___x_4508_, v___y_4551_);
v___x_4567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4562_, v___x_4567_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_dec_ref(v___x_4568_);
v___y_4510_ = v___x_4562_;
v___y_4511_ = v___y_4550_;
v___y_4512_ = v___y_4552_;
v___y_4513_ = v___y_4553_;
v___y_4514_ = v___y_4554_;
v___y_4515_ = v___y_4555_;
v___y_4516_ = v___y_4556_;
v___y_4517_ = v___y_4557_;
goto v___jp_4509_;
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4550_);
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4568_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4568_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4550_);
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4577_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4558_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4558_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
v___jp_4585_:
{
uint8_t v_isNoncomputableSection_4594_; 
v_isNoncomputableSection_4594_ = lean_ctor_get_uint8(v___y_4588_, sizeof(void*)*8 + 4);
if (v_isNoncomputableSection_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4595_ = lean_unsigned_to_nat(1u);
v___x_4596_ = lean_mk_empty_array_with_capacity(v___x_4595_);
lean_inc(v___x_4508_);
v___x_4597_ = lean_array_push(v___x_4596_, v___x_4508_);
v___x_4598_ = l_Lean_compileDecls(v___x_4597_, v___x_4481_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_dec_ref(v___x_4598_);
v___y_4550_ = v___y_4586_;
v___y_4551_ = v___y_4587_;
v___y_4552_ = v___y_4588_;
v___y_4553_ = v___y_4589_;
v___y_4554_ = v___y_4590_;
v___y_4555_ = v___y_4591_;
v___y_4556_ = v___y_4592_;
v___y_4557_ = v___y_4593_;
goto v___jp_4549_;
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4586_);
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
else
{
v___y_4550_ = v___y_4586_;
v___y_4551_ = v___y_4587_;
v___y_4552_ = v___y_4588_;
v___y_4553_ = v___y_4589_;
v___y_4554_ = v___y_4590_;
v___y_4555_ = v___y_4591_;
v___y_4556_ = v___y_4592_;
v___y_4557_ = v___y_4593_;
goto v___jp_4549_;
}
}
v___jp_4607_:
{
lean_object* v_snd_4609_; lean_object* v_fst_4610_; lean_object* v_fst_4611_; lean_object* v_snd_4612_; lean_object* v___x_4613_; lean_object* v_toConstantVal_4614_; lean_object* v_env_4615_; lean_object* v_levelParams_4616_; uint32_t v___x_4617_; uint32_t v___x_4618_; uint32_t v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4677_; 
v_snd_4609_ = lean_ctor_get(v_a_4608_, 1);
lean_inc(v_snd_4609_);
v_fst_4610_ = lean_ctor_get(v_a_4608_, 0);
lean_inc(v_fst_4610_);
lean_dec_ref(v_a_4608_);
v_fst_4611_ = lean_ctor_get(v_snd_4609_, 0);
lean_inc_n(v_fst_4611_, 2);
v_snd_4612_ = lean_ctor_get(v_snd_4609_, 1);
lean_inc(v_snd_4612_);
lean_dec(v_snd_4609_);
v___x_4613_ = lean_st_ref_get(v___y_4491_);
v_toConstantVal_4614_ = lean_ctor_get(v_a_4503_, 0);
lean_inc_ref(v_toConstantVal_4614_);
lean_dec(v_a_4503_);
v_env_4615_ = lean_ctor_get(v___x_4613_, 0);
lean_inc_ref(v_env_4615_);
lean_dec(v___x_4613_);
v_levelParams_4616_ = lean_ctor_get(v_toConstantVal_4614_, 1);
lean_inc(v_levelParams_4616_);
lean_dec_ref(v_toConstantVal_4614_);
v___x_4617_ = l_Lean_getMaxHeight(v_env_4615_, v_fst_4611_);
v___x_4618_ = 1;
v___x_4619_ = lean_uint32_add(v___x_4617_, v___x_4618_);
v___x_4620_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4620_, 0, v___x_4619_);
lean_inc(v___x_4508_);
v___x_4621_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4508_, v_levelParams_4616_, v_fst_4610_, v_fst_4611_, v___x_4620_, v___y_4491_);
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4624_ = v___x_4621_;
v_isShared_4625_ = v_isSharedCheck_4677_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4621_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4677_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
lean_ctor_set_tag(v___x_4624_, 1);
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
uint8_t v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = 0;
v___x_4629_ = l_Lean_addDecl(v___x_4627_, v___x_4628_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v___x_4630_; lean_object* v_env_4631_; uint8_t v___x_4632_; 
lean_dec_ref(v___x_4629_);
v___x_4630_ = lean_st_ref_get(v___y_4491_);
v_env_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc_ref(v_env_4631_);
lean_dec(v___x_4630_);
lean_inc(v_inductiveTypeName_4480_);
v___x_4632_ = l_Lean_isMarkedMeta(v_env_4631_, v_inductiveTypeName_4480_);
if (v___x_4632_ == 0)
{
v___y_4586_ = v_snd_4612_;
v___y_4587_ = v___x_4628_;
v___y_4588_ = v___y_4486_;
v___y_4589_ = v___y_4487_;
v___y_4590_ = v___y_4488_;
v___y_4591_ = v___y_4489_;
v___y_4592_ = v___y_4490_;
v___y_4593_ = v___y_4491_;
goto v___jp_4585_;
}
else
{
lean_object* v___x_4633_; lean_object* v_env_4634_; lean_object* v_nextMacroScope_4635_; lean_object* v_ngen_4636_; lean_object* v_auxDeclNGen_4637_; lean_object* v_traceState_4638_; lean_object* v_messages_4639_; lean_object* v_infoState_4640_; lean_object* v_snapshotTasks_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4666_; 
v___x_4633_ = lean_st_ref_take(v___y_4491_);
v_env_4634_ = lean_ctor_get(v___x_4633_, 0);
v_nextMacroScope_4635_ = lean_ctor_get(v___x_4633_, 1);
v_ngen_4636_ = lean_ctor_get(v___x_4633_, 2);
v_auxDeclNGen_4637_ = lean_ctor_get(v___x_4633_, 3);
v_traceState_4638_ = lean_ctor_get(v___x_4633_, 4);
v_messages_4639_ = lean_ctor_get(v___x_4633_, 6);
v_infoState_4640_ = lean_ctor_get(v___x_4633_, 7);
v_snapshotTasks_4641_ = lean_ctor_get(v___x_4633_, 8);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4666_ == 0)
{
lean_object* v_unused_4667_; 
v_unused_4667_ = lean_ctor_get(v___x_4633_, 5);
lean_dec(v_unused_4667_);
v___x_4643_ = v___x_4633_;
v_isShared_4644_ = v_isSharedCheck_4666_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_snapshotTasks_4641_);
lean_inc(v_infoState_4640_);
lean_inc(v_messages_4639_);
lean_inc(v_traceState_4638_);
lean_inc(v_auxDeclNGen_4637_);
lean_inc(v_ngen_4636_);
lean_inc(v_nextMacroScope_4635_);
lean_inc(v_env_4634_);
lean_dec(v___x_4633_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4666_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
lean_inc(v___x_4508_);
v___x_4645_ = l_Lean_markMeta(v_env_4634_, v___x_4508_);
v___x_4646_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4644_ == 0)
{
lean_ctor_set(v___x_4643_, 5, v___x_4646_);
lean_ctor_set(v___x_4643_, 0, v___x_4645_);
v___x_4648_ = v___x_4643_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v_nextMacroScope_4635_);
lean_ctor_set(v_reuseFailAlloc_4665_, 2, v_ngen_4636_);
lean_ctor_set(v_reuseFailAlloc_4665_, 3, v_auxDeclNGen_4637_);
lean_ctor_set(v_reuseFailAlloc_4665_, 4, v_traceState_4638_);
lean_ctor_set(v_reuseFailAlloc_4665_, 5, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4665_, 6, v_messages_4639_);
lean_ctor_set(v_reuseFailAlloc_4665_, 7, v_infoState_4640_);
lean_ctor_set(v_reuseFailAlloc_4665_, 8, v_snapshotTasks_4641_);
v___x_4648_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v_mctx_4651_; lean_object* v_zetaDeltaFVarIds_4652_; lean_object* v_postponed_4653_; lean_object* v_diag_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4663_; 
v___x_4649_ = lean_st_ref_set(v___y_4491_, v___x_4648_);
v___x_4650_ = lean_st_ref_take(v___y_4489_);
v_mctx_4651_ = lean_ctor_get(v___x_4650_, 0);
v_zetaDeltaFVarIds_4652_ = lean_ctor_get(v___x_4650_, 2);
v_postponed_4653_ = lean_ctor_get(v___x_4650_, 3);
v_diag_4654_ = lean_ctor_get(v___x_4650_, 4);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4663_ == 0)
{
lean_object* v_unused_4664_; 
v_unused_4664_ = lean_ctor_get(v___x_4650_, 1);
lean_dec(v_unused_4664_);
v___x_4656_ = v___x_4650_;
v_isShared_4657_ = v_isSharedCheck_4663_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_diag_4654_);
lean_inc(v_postponed_4653_);
lean_inc(v_zetaDeltaFVarIds_4652_);
lean_inc(v_mctx_4651_);
lean_dec(v___x_4650_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4663_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4658_; lean_object* v___x_4660_; 
v___x_4658_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 1, v___x_4658_);
v___x_4660_ = v___x_4656_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_mctx_4651_);
lean_ctor_set(v_reuseFailAlloc_4662_, 1, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4662_, 2, v_zetaDeltaFVarIds_4652_);
lean_ctor_set(v_reuseFailAlloc_4662_, 3, v_postponed_4653_);
lean_ctor_set(v_reuseFailAlloc_4662_, 4, v_diag_4654_);
v___x_4660_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4661_; 
v___x_4661_ = lean_st_ref_set(v___y_4489_, v___x_4660_);
v___y_4586_ = v_snd_4612_;
v___y_4587_ = v___x_4628_;
v___y_4588_ = v___y_4486_;
v___y_4589_ = v___y_4487_;
v___y_4590_ = v___y_4488_;
v___y_4591_ = v___y_4489_;
v___y_4592_ = v___y_4490_;
v___y_4593_ = v___y_4491_;
goto v___jp_4585_;
}
}
}
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
lean_dec(v_snd_4612_);
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4668_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4629_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4629_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
}
v___jp_4678_:
{
if (lean_obj_tag(v___y_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4689_; 
v_a_4680_ = lean_ctor_get(v___y_4679_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___y_4679_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4682_ = v___y_4679_;
v_isShared_4683_ = v_isSharedCheck_4689_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___y_4679_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4689_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
if (lean_obj_tag(v_a_4680_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4686_; 
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v_a_4503_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4684_ = lean_ctor_get(v_a_4680_, 0);
lean_inc(v_a_4684_);
lean_dec_ref(v_a_4680_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v_a_4684_);
v___x_4686_ = v___x_4682_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
else
{
lean_object* v_a_4688_; 
lean_del_object(v___x_4682_);
v_a_4688_ = lean_ctor_get(v_a_4680_, 0);
lean_inc(v_a_4688_);
lean_dec_ref(v_a_4680_);
v_a_4608_ = v_a_4688_;
goto v___jp_4607_;
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
lean_dec(v___x_4508_);
lean_dec(v_instName_4504_);
lean_dec(v_a_4503_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4690_ = lean_ctor_get(v___y_4679_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___y_4679_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___y_4679_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___y_4679_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_dec(v_a_4498_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v___f_4485_);
lean_dec(v_ctorName_4483_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4735_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4502_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4502_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v___f_4485_);
lean_dec(v_ctorName_4483_);
lean_dec(v_inductiveTypeName_4480_);
v_a_4743_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4497_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4497_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
v___jp_4493_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___y_4494_);
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
return v___x_4496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4751_, lean_object* v___x_4752_, lean_object* v_inductiveTypeName_4753_, lean_object* v___x_4754_, lean_object* v___x_4755_, lean_object* v_ctorName_4756_, lean_object* v_addHypotheses_4757_, lean_object* v___f_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
uint8_t v___x_17162__boxed_4766_; uint8_t v_addHypotheses_boxed_4767_; lean_object* v_res_4768_; 
v___x_17162__boxed_4766_ = lean_unbox(v___x_4754_);
v_addHypotheses_boxed_4767_ = lean_unbox(v_addHypotheses_4757_);
v_res_4768_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4751_, v___x_4752_, v_inductiveTypeName_4753_, v___x_17162__boxed_4766_, v___x_4755_, v_ctorName_4756_, v_addHypotheses_boxed_4767_, v___f_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___x_4755_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4771_, lean_object* v_ctorName_4772_, uint8_t v_addHypotheses_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v___f_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; uint8_t v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___f_4788_; uint8_t v___x_4789_; 
v___f_4781_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4782_ = lean_box(0);
v___x_4783_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4784_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4785_ = 1;
v___x_4786_ = lean_box(v___x_4785_);
v___x_4787_ = lean_box(v_addHypotheses_4773_);
lean_inc(v_ctorName_4772_);
v___f_4788_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4788_, 0, v___x_4783_);
lean_closure_set(v___f_4788_, 1, v___x_4784_);
lean_closure_set(v___f_4788_, 2, v_inductiveTypeName_4771_);
lean_closure_set(v___f_4788_, 3, v___x_4786_);
lean_closure_set(v___f_4788_, 4, v___x_4782_);
lean_closure_set(v___f_4788_, 5, v_ctorName_4772_);
lean_closure_set(v___f_4788_, 6, v___x_4787_);
lean_closure_set(v___f_4788_, 7, v___f_4781_);
v___x_4789_ = l_Lean_isPrivateName(v_ctorName_4772_);
lean_dec(v_ctorName_4772_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
v___x_4790_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4788_, v___x_4785_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
return v___x_4790_;
}
else
{
uint8_t v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = 0;
v___x_4792_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4788_, v___x_4791_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
return v___x_4792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4793_, lean_object* v_ctorName_4794_, lean_object* v_addHypotheses_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_){
_start:
{
uint8_t v_addHypotheses_boxed_4803_; lean_object* v_res_4804_; 
v_addHypotheses_boxed_4803_ = lean_unbox(v_addHypotheses_4795_);
v_res_4804_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4793_, v_ctorName_4794_, v_addHypotheses_boxed_4803_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
lean_dec(v_a_4799_);
lean_dec_ref(v_a_4798_);
lean_dec(v_a_4797_);
lean_dec_ref(v_a_4796_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4805_, lean_object* v_ctorName_4806_, uint8_t v_addHypotheses_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4811_ = lean_box(v_addHypotheses_4807_);
v___x_4812_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4812_, 0, v_inductiveTypeName_4805_);
lean_closure_set(v___x_4812_, 1, v_ctorName_4806_);
lean_closure_set(v___x_4812_, 2, v___x_4811_);
v___x_4813_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4812_, v_a_4808_, v_a_4809_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4843_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4843_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4843_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
if (lean_obj_tag(v_a_4814_) == 0)
{
uint8_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
v___x_4818_ = 0;
v___x_4819_ = lean_box(v___x_4818_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v___x_4819_);
v___x_4821_ = v___x_4816_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
else
{
lean_object* v_val_4823_; lean_object* v___x_4824_; 
lean_del_object(v___x_4816_);
v_val_4823_ = lean_ctor_get(v_a_4814_, 0);
lean_inc(v_val_4823_);
lean_dec_ref(v_a_4814_);
v___x_4824_ = l_Lean_Elab_Command_elabCommand(v_val_4823_, v_a_4808_, v_a_4809_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4833_; 
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4833_ == 0)
{
lean_object* v_unused_4834_; 
v_unused_4834_ = lean_ctor_get(v___x_4824_, 0);
lean_dec(v_unused_4834_);
v___x_4826_ = v___x_4824_;
v_isShared_4827_ = v_isSharedCheck_4833_;
goto v_resetjp_4825_;
}
else
{
lean_dec(v___x_4824_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4833_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
uint8_t v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4828_ = 1;
v___x_4829_ = lean_box(v___x_4828_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v___x_4829_);
v___x_4831_ = v___x_4826_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
v_a_4835_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4824_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4824_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
v_a_4844_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4813_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4813_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4852_, lean_object* v_ctorName_4853_, lean_object* v_addHypotheses_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
uint8_t v_addHypotheses_boxed_4858_; lean_object* v_res_4859_; 
v_addHypotheses_boxed_4858_ = lean_unbox(v_addHypotheses_4854_);
v_res_4859_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4852_, v_ctorName_4853_, v_addHypotheses_boxed_4858_, v_a_4855_, v_a_4856_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4863_, uint8_t v_addHypotheses_4864_, lean_object* v_as_x27_4865_, lean_object* v_b_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
if (lean_obj_tag(v_as_x27_4865_) == 0)
{
lean_object* v___x_4870_; 
lean_dec(v_declName_4863_);
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v_b_4866_);
return v___x_4870_;
}
else
{
lean_object* v_head_4871_; lean_object* v_tail_4872_; lean_object* v___x_4873_; 
lean_dec_ref(v_b_4866_);
v_head_4871_ = lean_ctor_get(v_as_x27_4865_, 0);
v_tail_4872_ = lean_ctor_get(v_as_x27_4865_, 1);
lean_inc(v_head_4871_);
lean_inc(v_declName_4863_);
v___x_4873_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4863_, v_head_4871_, v_addHypotheses_4864_, v___y_4867_, v___y_4868_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4887_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4887_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4887_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4878_ = lean_box(0);
v___x_4879_ = lean_unbox(v_a_4874_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; 
lean_del_object(v___x_4876_);
lean_dec(v_a_4874_);
v___x_4880_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v_as_x27_4865_ = v_tail_4872_;
v_b_4866_ = v___x_4880_;
goto _start;
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4885_; 
lean_dec(v_declName_4863_);
v___x_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4882_, 0, v_a_4874_);
v___x_4883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
lean_ctor_set(v___x_4883_, 1, v___x_4878_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v___x_4883_);
v___x_4885_ = v___x_4876_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
else
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
lean_dec(v_declName_4863_);
v_a_4888_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4873_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4873_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4896_, lean_object* v_addHypotheses_4897_, lean_object* v_as_x27_4898_, lean_object* v_b_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
uint8_t v_addHypotheses_boxed_4903_; lean_object* v_res_4904_; 
v_addHypotheses_boxed_4903_ = lean_unbox(v_addHypotheses_4897_);
v_res_4904_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4896_, v_addHypotheses_boxed_4903_, v_as_x27_4898_, v_b_4899_, v___y_4900_, v___y_4901_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec(v_as_x27_4898_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4905_, lean_object* v_declName_4906_, uint8_t v_addHypotheses_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v_ctors_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v_ctors_4911_ = lean_ctor_get(v_a_4905_, 4);
v___x_4912_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4913_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4906_, v_addHypotheses_4907_, v_ctors_4911_, v___x_4912_, v___y_4908_, v___y_4909_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4928_; 
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4916_ = v___x_4913_;
v_isShared_4917_ = v_isSharedCheck_4928_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4913_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4928_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v_fst_4918_; 
v_fst_4918_ = lean_ctor_get(v_a_4914_, 0);
lean_inc(v_fst_4918_);
lean_dec(v_a_4914_);
if (lean_obj_tag(v_fst_4918_) == 0)
{
uint8_t v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4922_; 
v___x_4919_ = 0;
v___x_4920_ = lean_box(v___x_4919_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v___x_4920_);
v___x_4922_ = v___x_4916_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4920_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
else
{
lean_object* v_val_4924_; lean_object* v___x_4926_; 
v_val_4924_ = lean_ctor_get(v_fst_4918_, 0);
lean_inc(v_val_4924_);
lean_dec_ref(v_fst_4918_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v_val_4924_);
v___x_4926_ = v___x_4916_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_val_4924_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
else
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
v_a_4929_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4931_ = v___x_4913_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4913_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_4937_, lean_object* v_declName_4938_, lean_object* v_addHypotheses_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
uint8_t v_addHypotheses_boxed_4943_; lean_object* v_res_4944_; 
v_addHypotheses_boxed_4943_ = lean_unbox(v_addHypotheses_4939_);
v_res_4944_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_4937_, v_declName_4938_, v_addHypotheses_boxed_4943_, v___y_4940_, v___y_4941_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_a_4937_);
return v_res_4944_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4945_; 
v___x_4945_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4945_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
return v___x_4947_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4948_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4949_ = lean_unsigned_to_nat(0u);
v___x_4950_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4949_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
lean_ctor_set(v___x_4950_, 2, v___x_4949_);
lean_ctor_set(v___x_4950_, 3, v___x_4949_);
lean_ctor_set(v___x_4950_, 4, v___x_4948_);
lean_ctor_set(v___x_4950_, 5, v___x_4948_);
lean_ctor_set(v___x_4950_, 6, v___x_4948_);
lean_ctor_set(v___x_4950_, 7, v___x_4948_);
lean_ctor_set(v___x_4950_, 8, v___x_4948_);
lean_ctor_set(v___x_4950_, 9, v___x_4948_);
return v___x_4950_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = lean_unsigned_to_nat(32u);
v___x_4952_ = lean_mk_empty_array_with_capacity(v___x_4951_);
v___x_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4952_);
return v___x_4953_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4954_ = ((size_t)5ULL);
v___x_4955_ = lean_unsigned_to_nat(0u);
v___x_4956_ = lean_unsigned_to_nat(32u);
v___x_4957_ = lean_mk_empty_array_with_capacity(v___x_4956_);
v___x_4958_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_4959_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4959_, 0, v___x_4958_);
lean_ctor_set(v___x_4959_, 1, v___x_4957_);
lean_ctor_set(v___x_4959_, 2, v___x_4955_);
lean_ctor_set(v___x_4959_, 3, v___x_4955_);
lean_ctor_set_usize(v___x_4959_, 4, v___x_4954_);
return v___x_4959_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4960_ = lean_box(1);
v___x_4961_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_4962_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
lean_ctor_set(v___x_4963_, 1, v___x_4961_);
lean_ctor_set(v___x_4963_, 2, v___x_4960_);
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v___x_4967_; lean_object* v_env_4968_; lean_object* v___x_4969_; lean_object* v_scopes_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v_opts_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4967_ = lean_st_ref_get(v___y_4965_);
v_env_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_ref(v_env_4968_);
lean_dec(v___x_4967_);
v___x_4969_ = lean_st_ref_get(v___y_4965_);
v_scopes_4970_ = lean_ctor_get(v___x_4969_, 2);
lean_inc(v_scopes_4970_);
lean_dec(v___x_4969_);
v___x_4971_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4972_ = l_List_head_x21___redArg(v___x_4971_, v_scopes_4970_);
lean_dec(v_scopes_4970_);
v_opts_4973_ = lean_ctor_get(v___x_4972_, 1);
lean_inc_ref(v_opts_4973_);
lean_dec(v___x_4972_);
v___x_4974_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_4975_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5);
v___x_4976_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4976_, 0, v_env_4968_);
lean_ctor_set(v___x_4976_, 1, v___x_4974_);
lean_ctor_set(v___x_4976_, 2, v___x_4975_);
lean_ctor_set(v___x_4976_, 3, v_opts_4973_);
v___x_4977_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
lean_ctor_set(v___x_4977_, 1, v_msgData_4964_);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_4979_, v___y_4980_);
lean_dec(v___y_4980_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_4983_, lean_object* v_macroStack_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v___x_4987_; lean_object* v_scopes_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v_opts_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v___x_4987_ = lean_st_ref_get(v___y_4985_);
v_scopes_4988_ = lean_ctor_get(v___x_4987_, 2);
lean_inc(v_scopes_4988_);
lean_dec(v___x_4987_);
v___x_4989_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4990_ = l_List_head_x21___redArg(v___x_4989_, v_scopes_4988_);
lean_dec(v_scopes_4988_);
v_opts_4991_ = lean_ctor_get(v___x_4990_, 1);
lean_inc_ref(v_opts_4991_);
lean_dec(v___x_4990_);
v___x_4992_ = l_Lean_Elab_pp_macroStack;
v___x_4993_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_4991_, v___x_4992_);
lean_dec_ref(v_opts_4991_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; 
lean_dec(v_macroStack_4984_);
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v_msgData_4983_);
return v___x_4994_;
}
else
{
if (lean_obj_tag(v_macroStack_4984_) == 0)
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v_msgData_4983_);
return v___x_4995_;
}
else
{
lean_object* v_head_4996_; lean_object* v_after_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5012_; 
v_head_4996_ = lean_ctor_get(v_macroStack_4984_, 0);
lean_inc(v_head_4996_);
v_after_4997_ = lean_ctor_get(v_head_4996_, 1);
v_isSharedCheck_5012_ = !lean_is_exclusive(v_head_4996_);
if (v_isSharedCheck_5012_ == 0)
{
lean_object* v_unused_5013_; 
v_unused_5013_ = lean_ctor_get(v_head_4996_, 0);
lean_dec(v_unused_5013_);
v___x_4999_ = v_head_4996_;
v_isShared_5000_ = v_isSharedCheck_5012_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_after_4997_);
lean_dec(v_head_4996_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5012_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5001_; lean_object* v___x_5003_; 
v___x_5001_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_5000_ == 0)
{
lean_ctor_set_tag(v___x_4999_, 7);
lean_ctor_set(v___x_4999_, 1, v___x_5001_);
lean_ctor_set(v___x_4999_, 0, v_msgData_4983_);
v___x_5003_ = v___x_4999_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_msgData_4983_);
lean_ctor_set(v_reuseFailAlloc_5011_, 1, v___x_5001_);
v___x_5003_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v_msgData_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5004_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_5005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5003_);
lean_ctor_set(v___x_5005_, 1, v___x_5004_);
v___x_5006_ = l_Lean_MessageData_ofSyntax(v_after_4997_);
v___x_5007_ = l_Lean_indentD(v___x_5006_);
v_msgData_5008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5008_, 0, v___x_5005_);
lean_ctor_set(v_msgData_5008_, 1, v___x_5007_);
v___x_5009_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_5008_, v_macroStack_4984_);
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
return v___x_5010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_5014_, lean_object* v_macroStack_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5014_, v_macroStack_5015_, v___y_5016_);
lean_dec(v___y_5016_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_Elab_Command_getRef___redArg(v___y_5020_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v_macroStack_5025_; lean_object* v___x_5026_; lean_object* v_a_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5038_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
lean_inc(v_a_5024_);
lean_dec_ref(v___x_5023_);
v_macroStack_5025_ = lean_ctor_get(v___y_5020_, 4);
v___x_5026_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_5019_, v___y_5021_);
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref(v___x_5026_);
v___x_5028_ = l_Lean_Elab_getBetterRef(v_a_5024_, v_macroStack_5025_);
lean_dec(v_a_5024_);
lean_inc(v_macroStack_5025_);
v___x_5029_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_5027_, v_macroStack_5025_, v___y_5021_);
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5032_ = v___x_5029_;
v_isShared_5033_ = v_isSharedCheck_5038_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_5029_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5038_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5028_);
lean_ctor_set(v___x_5034_, 1, v_a_5030_);
if (v_isShared_5033_ == 0)
{
lean_ctor_set_tag(v___x_5032_, 1);
lean_ctor_set(v___x_5032_, 0, v___x_5034_);
v___x_5036_ = v___x_5032_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
lean_dec_ref(v_msg_5019_);
v_a_5039_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5023_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5023_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5047_, v___y_5048_, v___y_5049_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v___x_5056_; lean_object* v_env_5057_; lean_object* v___x_5058_; 
v___x_5056_ = lean_st_ref_get(v___y_5054_);
v_env_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc_ref(v_env_5057_);
lean_dec(v___x_5056_);
lean_inc(v_constName_5052_);
v___x_5058_ = l_Lean_isInductiveCore_x3f(v_env_5057_, v_constName_5052_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v___x_5059_; uint8_t v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5059_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5060_ = 0;
v___x_5061_ = l_Lean_MessageData_ofConstName(v_constName_5052_, v___x_5060_);
v___x_5062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5059_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
v___x_5063_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5062_);
lean_ctor_set(v___x_5064_, 1, v___x_5063_);
v___x_5065_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5064_, v___y_5053_, v___y_5054_);
return v___x_5065_;
}
else
{
lean_object* v_val_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5073_; 
lean_dec(v_constName_5052_);
v_val_5066_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5068_ = v___x_5058_;
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_val_5066_);
lean_dec(v___x_5058_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5071_; 
if (v_isShared_5069_ == 0)
{
lean_ctor_set_tag(v___x_5068_, 0);
v___x_5071_ = v___x_5068_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_val_5066_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
return v_res_5078_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5080_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5081_ = l_Lean_stringToMessageData(v___x_5080_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
lean_object* v___x_5089_; 
lean_inc(v_declName_5082_);
v___x_5089_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5082_, v___y_5083_, v___y_5084_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v_a_5090_; uint8_t v___x_5091_; lean_object* v___x_5092_; 
v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
lean_inc(v_a_5090_);
lean_dec_ref(v___x_5089_);
v___x_5091_ = 0;
lean_inc(v_declName_5082_);
v___x_5092_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5090_, v_declName_5082_, v___x_5091_, v___y_5083_, v___y_5084_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v_a_5093_; uint8_t v___x_5094_; 
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
lean_inc(v_a_5093_);
lean_dec_ref(v___x_5092_);
v___x_5094_ = lean_unbox(v_a_5093_);
lean_dec(v_a_5093_);
if (v___x_5094_ == 0)
{
uint8_t v___x_5095_; lean_object* v___x_5096_; 
v___x_5095_ = 1;
lean_inc(v_declName_5082_);
v___x_5096_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5090_, v_declName_5082_, v___x_5095_, v___y_5083_, v___y_5084_);
lean_dec(v_a_5090_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; uint8_t v___x_5098_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_a_5097_);
lean_dec_ref(v___x_5096_);
v___x_5098_ = lean_unbox(v_a_5097_);
lean_dec(v_a_5097_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5099_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5100_ = l_Lean_MessageData_ofConstName(v_declName_5082_, v___x_5091_);
v___x_5101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5099_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5101_);
lean_ctor_set(v___x_5103_, 1, v___x_5102_);
v___x_5104_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5103_, v___y_5083_, v___y_5084_);
return v___x_5104_;
}
else
{
lean_dec(v_declName_5082_);
goto v___jp_5086_;
}
}
else
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5112_; 
lean_dec(v_declName_5082_);
v_a_5105_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5112_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5112_ == 0)
{
v___x_5107_ = v___x_5096_;
v_isShared_5108_ = v_isSharedCheck_5112_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___x_5096_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5112_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v___x_5110_; 
if (v_isShared_5108_ == 0)
{
v___x_5110_ = v___x_5107_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v_a_5105_);
v___x_5110_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
return v___x_5110_;
}
}
}
}
else
{
lean_dec(v_a_5090_);
lean_dec(v_declName_5082_);
goto v___jp_5086_;
}
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec(v_a_5090_);
lean_dec(v_declName_5082_);
v_a_5113_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5092_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5092_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_dec(v_declName_5082_);
v_a_5121_ = lean_ctor_get(v___x_5089_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5089_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5089_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
v___jp_5086_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5087_ = lean_box(0);
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v___x_5087_);
return v___x_5088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5129_, v___y_5130_, v___y_5131_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_){
_start:
{
lean_object* v___f_5138_; lean_object* v___x_5139_; 
lean_inc(v_declName_5134_);
v___f_5138_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5138_, 0, v_declName_5134_);
v___x_5139_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5134_, v___f_5138_, v_a_5135_, v_a_5136_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5140_, v_a_5141_, v_a_5142_);
lean_dec(v_a_5142_);
lean_dec_ref(v_a_5141_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5145_, uint8_t v_addHypotheses_5146_, lean_object* v_as_5147_, lean_object* v_as_x27_5148_, lean_object* v_b_5149_, lean_object* v_a_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5145_, v_addHypotheses_5146_, v_as_x27_5148_, v_b_5149_, v___y_5151_, v___y_5152_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5155_, lean_object* v_addHypotheses_5156_, lean_object* v_as_5157_, lean_object* v_as_x27_5158_, lean_object* v_b_5159_, lean_object* v_a_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
uint8_t v_addHypotheses_boxed_5164_; lean_object* v_res_5165_; 
v_addHypotheses_boxed_5164_ = lean_unbox(v_addHypotheses_5156_);
v_res_5165_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5155_, v_addHypotheses_boxed_5164_, v_as_5157_, v_as_x27_5158_, v_b_5159_, v_a_5160_, v___y_5161_, v___y_5162_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v_as_x27_5158_);
lean_dec(v_as_5157_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_){
_start:
{
lean_object* v___x_5170_; 
v___x_5170_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5166_, v___y_5168_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5171_, v___y_5172_, v___y_5173_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5176_, lean_object* v_msg_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
lean_object* v___x_5181_; 
v___x_5181_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5177_, v___y_5178_, v___y_5179_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5182_, lean_object* v_msg_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5182_, v_msg_5183_, v___y_5184_, v___y_5185_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5188_, lean_object* v_macroStack_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5188_, v_macroStack_5189_, v___y_5191_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5194_, lean_object* v_macroStack_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
lean_object* v_res_5199_; 
v_res_5199_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5194_, v_macroStack_5195_, v___y_5196_, v___y_5197_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
return v_res_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5200_, lean_object* v___y_5201_){
_start:
{
lean_object* v___x_5203_; lean_object* v_env_5204_; uint8_t v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5203_ = lean_st_ref_get(v___y_5201_);
v_env_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc_ref(v_env_5204_);
lean_dec(v___x_5203_);
v___x_5205_ = l_Lean_isInductiveCore(v_env_5204_, v_declName_5200_);
v___x_5206_ = lean_box(v___x_5205_);
v___x_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5206_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5208_, v___y_5209_);
lean_dec(v___y_5209_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5212_, v___y_5214_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5217_, v___y_5218_, v___y_5219_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_){
_start:
{
if (v_____do__lift_5222_ == 0)
{
uint8_t v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; 
v___x_5226_ = 1;
v___x_5227_ = lean_box(v___x_5226_);
v___x_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5227_);
return v___x_5228_;
}
else
{
uint8_t v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v___x_5229_ = 0;
v___x_5230_ = lean_box(v___x_5229_);
v___x_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5231_, 0, v___x_5230_);
return v___x_5231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
uint8_t v_____do__lift_1703__boxed_5236_; lean_object* v_res_5237_; 
v_____do__lift_1703__boxed_5236_ = lean_unbox(v_____do__lift_5232_);
v_res_5237_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1703__boxed_5236_, v___y_5233_, v___y_5234_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5238_, size_t v_i_5239_, size_t v_stop_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
uint8_t v___x_5244_; 
v___x_5244_ = lean_usize_dec_eq(v_i_5239_, v_stop_5240_);
if (v___x_5244_ == 0)
{
uint8_t v___x_5245_; uint8_t v_a_5247_; lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5245_ = 1;
v___x_5253_ = lean_array_uget_borrowed(v_as_5238_, v_i_5239_);
lean_inc(v___x_5253_);
v___x_5254_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5253_, v___y_5242_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5264_; 
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5257_ = v___x_5254_;
v_isShared_5258_ = v_isSharedCheck_5264_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5254_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5264_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
uint8_t v___x_5259_; 
v___x_5259_ = lean_unbox(v_a_5255_);
lean_dec(v_a_5255_);
if (v___x_5259_ == 0)
{
lean_object* v___x_5260_; lean_object* v___x_5262_; 
v___x_5260_ = lean_box(v___x_5245_);
if (v_isShared_5258_ == 0)
{
lean_ctor_set(v___x_5257_, 0, v___x_5260_);
v___x_5262_ = v___x_5257_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5260_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
else
{
lean_del_object(v___x_5257_);
v_a_5247_ = v___x_5244_;
goto v___jp_5246_;
}
}
}
else
{
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_a_5265_; uint8_t v___x_5266_; 
v_a_5265_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_a_5265_);
lean_dec_ref(v___x_5254_);
v___x_5266_ = lean_unbox(v_a_5265_);
lean_dec(v_a_5265_);
v_a_5247_ = v___x_5266_;
goto v___jp_5246_;
}
else
{
return v___x_5254_;
}
}
v___jp_5246_:
{
if (v_a_5247_ == 0)
{
size_t v___x_5248_; size_t v___x_5249_; 
v___x_5248_ = ((size_t)1ULL);
v___x_5249_ = lean_usize_add(v_i_5239_, v___x_5248_);
v_i_5239_ = v___x_5249_;
goto _start;
}
else
{
lean_object* v___x_5251_; lean_object* v___x_5252_; 
v___x_5251_ = lean_box(v___x_5245_);
v___x_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5251_);
return v___x_5252_;
}
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
lean_dec_ref(v___x_5288_);
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
uint8_t v___y_5309_; lean_object* v___y_5310_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___y_5346_; uint8_t v___x_5349_; 
v___x_5328_ = lean_unsigned_to_nat(0u);
v___x_5329_ = lean_array_get_size(v_declNames_5304_);
v___x_5349_ = lean_nat_dec_lt(v___x_5328_, v___x_5329_);
if (v___x_5349_ == 0)
{
lean_object* v___x_5350_; 
v___x_5350_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5349_, v_a_5305_, v_a_5306_);
v___y_5346_ = v___x_5350_;
goto v___jp_5345_;
}
else
{
if (v___x_5349_ == 0)
{
goto v___jp_5330_;
}
else
{
size_t v___x_5351_; size_t v___x_5352_; lean_object* v___x_5353_; 
v___x_5351_ = ((size_t)0ULL);
v___x_5352_ = lean_usize_of_nat(v___x_5329_);
v___x_5353_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5304_, v___x_5351_, v___x_5352_, v_a_5305_, v_a_5306_);
if (lean_obj_tag(v___x_5353_) == 0)
{
lean_object* v_a_5354_; uint8_t v___x_5355_; lean_object* v___x_5356_; 
v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc(v_a_5354_);
lean_dec_ref(v___x_5353_);
v___x_5355_ = lean_unbox(v_a_5354_);
lean_dec(v_a_5354_);
v___x_5356_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5355_, v_a_5305_, v_a_5306_);
v___y_5346_ = v___x_5356_;
goto v___jp_5345_;
}
else
{
v___y_5346_ = v___x_5353_;
goto v___jp_5345_;
}
}
}
v___jp_5308_:
{
if (lean_obj_tag(v___y_5310_) == 0)
{
lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5318_; 
v_isSharedCheck_5318_ = !lean_is_exclusive(v___y_5310_);
if (v_isSharedCheck_5318_ == 0)
{
lean_object* v_unused_5319_; 
v_unused_5319_ = lean_ctor_get(v___y_5310_, 0);
lean_dec(v_unused_5319_);
v___x_5312_ = v___y_5310_;
v_isShared_5313_ = v_isSharedCheck_5318_;
goto v_resetjp_5311_;
}
else
{
lean_dec(v___y_5310_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5318_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5314_; lean_object* v___x_5316_; 
v___x_5314_ = lean_box(v___y_5309_);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5314_);
v___x_5316_ = v___x_5312_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5314_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
v_a_5320_ = lean_ctor_get(v___y_5310_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___y_5310_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___y_5310_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___y_5310_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
}
v___jp_5330_:
{
uint8_t v___x_5331_; uint8_t v___x_5332_; 
v___x_5331_ = 1;
v___x_5332_ = lean_nat_dec_lt(v___x_5328_, v___x_5329_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5333_ = lean_box(v___x_5331_);
v___x_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5333_);
return v___x_5334_;
}
else
{
lean_object* v___x_5335_; uint8_t v___x_5336_; 
v___x_5335_ = lean_box(0);
v___x_5336_ = lean_nat_dec_le(v___x_5329_, v___x_5329_);
if (v___x_5336_ == 0)
{
if (v___x_5332_ == 0)
{
lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5337_ = lean_box(v___x_5331_);
v___x_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5337_);
return v___x_5338_;
}
else
{
size_t v___x_5339_; size_t v___x_5340_; lean_object* v___x_5341_; 
v___x_5339_ = ((size_t)0ULL);
v___x_5340_ = lean_usize_of_nat(v___x_5329_);
v___x_5341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5304_, v___x_5339_, v___x_5340_, v___x_5335_, v_a_5305_, v_a_5306_);
v___y_5309_ = v___x_5331_;
v___y_5310_ = v___x_5341_;
goto v___jp_5308_;
}
}
else
{
size_t v___x_5342_; size_t v___x_5343_; lean_object* v___x_5344_; 
v___x_5342_ = ((size_t)0ULL);
v___x_5343_ = lean_usize_of_nat(v___x_5329_);
v___x_5344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5304_, v___x_5342_, v___x_5343_, v___x_5335_, v_a_5305_, v_a_5306_);
v___y_5309_ = v___x_5331_;
v___y_5310_ = v___x_5344_;
goto v___jp_5308_;
}
}
}
v___jp_5345_:
{
if (lean_obj_tag(v___y_5346_) == 0)
{
lean_object* v_a_5347_; uint8_t v___x_5348_; 
v_a_5347_ = lean_ctor_get(v___y_5346_, 0);
v___x_5348_ = lean_unbox(v_a_5347_);
if (v___x_5348_ == 0)
{
return v___y_5346_;
}
else
{
lean_dec_ref(v___y_5346_);
goto v___jp_5330_;
}
}
else
{
return v___y_5346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_){
_start:
{
lean_object* v_res_5361_; 
v_res_5361_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5357_, v_a_5358_, v_a_5359_);
lean_dec(v_a_5359_);
lean_dec_ref(v_a_5358_);
lean_dec_ref(v_declNames_5357_);
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5426_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5427_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5428_ = l_Lean_Elab_registerDerivingHandler(v___x_5426_, v___x_5427_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v___x_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; 
lean_dec_ref(v___x_5428_);
v___x_5429_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5430_ = 0;
v___x_5431_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5432_ = l_Lean_registerTraceClass(v___x_5429_, v___x_5430_, v___x_5431_);
return v___x_5432_;
}
else
{
return v___x_5428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5434_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Inhabited(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
